import BstLean.Part268CellShard14Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12700_20 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (4169059363057 / 5000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (140721843453 / 6250000000000 : ℝ))
      (E := (cell12700 ⟨20, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (4169059363057 / 5000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (140721843453 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_21 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83346704226239 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251553516817 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨21, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83346704226239 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251553516817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_22 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41656122715369 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125778758993 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨22, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41656122715369 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125778758993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_23 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83277810841753 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251561502507 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨23, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83277810841753 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251561502507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_24 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83243400426571 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (112578276613 / 5000000000000 : ℝ))
      (E := (cell12700 ⟨24, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83243400426571 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (112578276613 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_25 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41604507076323 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251569493803 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨25, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41604507076323 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251569493803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_26 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83174651987599 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (17590418023 / 781250000000 : ℝ))
      (E := (cell12700 ⟨26, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83174651987599 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (17590418023 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_27 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83140313899219 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125788758059 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨27, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83140313899219 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125788758059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_28 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83105999855457 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251581523901 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨28, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83105999855457 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251581523901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_29 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83071709824429 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251585532637 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨29, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83071709824429 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251585532637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_30 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41518721887207 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251589544441 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨30, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41518721887207 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251589544441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_31 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41501600836927 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125796780597 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨31, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41501600836927 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125796780597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_32 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (1659379669827 / 2000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125798762997 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨32, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (1659379669827 / 2000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125798762997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_33 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82934789195663 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251601557363 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨33, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82934789195663 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251601557363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_34 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16580123751143 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251605539359 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨34, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16580123751143 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251605539359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_35 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16573294428117 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562902382879 / 25000000000000 : ℝ))
      (E := (cell12700 ⟨35, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16573294428117 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562902382879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_36 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82832349319507 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450322706917 / 20000000000000 : ℝ))
      (E := (cell12700 ⟨36, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82832349319507 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450322706917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_37 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41399125130937 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225161754909 / 10000000000000 : ℝ))
      (E := (cell12700 ⟨37, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41399125130937 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225161754909 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_38 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (5172760933577 / 6250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125810787667 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨38, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (5172760933577 / 6250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125810787667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_39 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (82730123315283 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251625554673 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨39, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (82730123315283 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251625554673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12701_20 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (16676235689827 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125713409281 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨20, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (16676235689827 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125713409281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_21 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20836673931353 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450286164141 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨21, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20836673931353 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450286164141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_22 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41656118620327 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251434803159 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨22, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41656118620327 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251434803159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_23 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (4163890148099 / 5000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251438828019 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨23, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (4163890148099 / 5000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251438828019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_24 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20810848214169 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562860695531 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨24, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20810848214169 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562860695531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_25 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41604503446099 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251446785469 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨25, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41604503446099 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251446785469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_26 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (10396830629521 / 12500000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450290168233 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨26, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (10396830629521 / 12500000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450290168233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_27 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41570153628187 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562863708801 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨27, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41570153628187 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562863708801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_28 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (8310599352077 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562864707139 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨28, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (8310599352077 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562864707139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_29 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (2595990743671 / 3125000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450292564713 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨29, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (2595990743671 / 3125000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450292564713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_30 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (2075935951369 / 2500000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281433352793 / 12500000000000 : ℝ))
      (E := (cell12701 ⟨30, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (2075935951369 / 2500000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281433352793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_31 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83003196261077 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125735413387 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨31, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83003196261077 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125735413387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_32 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (648195143633 / 781250000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140717177407 / 6250000000000 : ℝ))
      (E := (cell12701 ⟨32, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (648195143633 / 781250000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140717177407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_33 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20733696098841 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251478858983 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨33, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20733696098841 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251478858983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_34 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41450307130509 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251482830781 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨34, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41450307130509 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251482830781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_35 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82866467951067 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251486813439 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨35, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82866467951067 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251486813439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_36 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82832345434747 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251490866359 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨36, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82832345434747 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251490866359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_37 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (82798246681449 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450298974557 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨37, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (82798246681449 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450298974557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_38 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41382085830361 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140718677059 / 6250000000000 : ℝ))
      (E := (cell12701 ⟨38, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41382085830361 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140718677059 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_39 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20682530085567 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281437858037 / 12500000000000 : ℝ))
      (E := (cell12701 ⟨39, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20682530085567 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281437858037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12702_20 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20845292409687 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (112565206897 / 5000000000000 : ℝ))
      (E := (cell12702 ⟨20, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20845292409687 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (112565206897 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_21 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16669337445233 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450261624139 / 20000000000000 : ℝ))
      (E := (cell12702 ⟨21, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16669337445233 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450261624139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_22 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83312229052113 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251312142797 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨22, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83312229052113 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251312142797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_23 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83277795083711 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251316149713 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨23, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83277795083711 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251316149713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_24 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (10405423161031 / 12500000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281415018119 / 12500000000000 : ℝ))
      (E := (cell12702 ⟨24, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (10405423161031 / 12500000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281415018119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_25 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83208999633179 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251324131789 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨25, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83208999633179 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251324131789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_26 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (5198414880383 / 6250000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251328113263 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨26, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (5198414880383 / 6250000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251328113263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_27 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20785075153721 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (70354129707 / 3125000000000 : ℝ))
      (E := (cell12702 ⟨27, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20785075153721 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (70354129707 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_28 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (415529935937 / 500000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (140708508099 / 6250000000000 : ℝ))
      (E := (cell12702 ⟨28, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (415529935937 / 500000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (140708508099 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_29 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16614339554359 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251340169393 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨29, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16614339554359 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251340169393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_30 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83037432336349 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281418019401 / 12500000000000 : ℝ))
      (E := (cell12702 ⟨30, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83037432336349 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281418019401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_31 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (2593849714047 / 3125000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251348147379 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨31, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (2593849714047 / 3125000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251348147379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_32 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16593794655973 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562838036889 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨32, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16593794655973 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562838036889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_33 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16586955919239 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251356157167 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨33, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16586955919239 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251356157167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_34 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16580121953483 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251360177411 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨34, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16580121953483 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251360177411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_35 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41433231881303 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251364150631 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨35, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41433231881303 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251364150631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_36 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41416170775503 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562842048703 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨36, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41416170775503 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562842048703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_37 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82798243102007 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125686096597 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨37, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82798243102007 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125686096597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_38 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82764168385159 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251376146007 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨38, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82764168385159 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251376146007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_39 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (82730117370163 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562845042677 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨39, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (82730117370163 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562845042677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12703_20 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41690580414989 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251181511663 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨20, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41690580414989 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251181511663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_21 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (5209167420531 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125592737547 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨21, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (5209167420531 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125592737547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_22 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (10414027608139 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112559473929 / 5000000000000 : ℝ))
      (E := (cell12703 ⟨22, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (10414027608139 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112559473929 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_23 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41638893603473 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562798366897 / 25000000000000 : ℝ))
      (E := (cell12703 ⟨23, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41638893603473 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562798366897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_24 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41621688860643 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (35174961 / 1562500000 : ℝ))
      (E := (cell12703 ⟨24, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41621688860643 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (35174961 / 1562500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_25 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83208992375589 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251201474367 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨25, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83208992375589 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251201474367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_26 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83174631137479 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125602749249 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨26, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83174631137479 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125602749249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_27 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83140293974747 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251209520823 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨27, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83140293974747 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251209520823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_28 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83105980855347 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251213485451 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨28, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83105980855347 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251213485451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_29 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83071691747397 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251217511633 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨29, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83071691747397 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251217511633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_30 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83037426619179 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562805371131 / 25000000000000 : ℝ))
      (E := (cell12703 ⟨30, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83037426619179 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562805371131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_31 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83003185439137 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251225523007 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨31, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83003185439137 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251225523007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_32 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41484484087937 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125614755843 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨32, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41484484087937 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125614755843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_33 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (20733693699539 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251233510499 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨33, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (20733693699539 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251233510499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_34 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (10362575659363 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450247504129 / 20000000000000 : ℝ))
      (E := (cell12703 ⟨34, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (10362575659363 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450247504129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_35 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82866459575201 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450248308619 / 20000000000000 : ℝ))
      (E := (cell12703 ⟨35, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82866459575201 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (450248308619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_36 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (20708084417071 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251245519943 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨36, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (20708084417071 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251245519943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_37 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (82798239523547 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (28140618879 / 1250000000000 : ℝ))
      (E := (cell12703 ⟨37, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (82798239523547 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (28140618879 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_38 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (4138208255527 / 5000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125626757263 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨38, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (4138208255527 / 5000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125626757263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_39 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41365057199483 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251257532637 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨39, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41365057199483 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251257532637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12704_20 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10422644002853 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562764720363 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨20, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10422644002853 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562764720363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_21 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83346670232407 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251062883899 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨21, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83346670232407 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251062883899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_22 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83312212679653 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (70345839651 / 3125000000000 : ℝ))
      (E := (cell12704 ⟨22, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83312212679653 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (70345839651 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_23 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20819444832921 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450214179669 / 20000000000000 : ℝ))
      (E := (cell12704 ⟨23, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20819444832921 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (450214179669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_24 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (8324337015579 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251074859269 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨24, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (8324337015579 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251074859269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_25 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83208985119427 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125539435801 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨25, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83208985119427 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125539435801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_26 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41587312095111 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251082880029 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨26, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41587312095111 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251082880029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_27 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20785071833991 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125543443679 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨27, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20785071833991 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125543443679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_28 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83105974524609 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251090896161 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨28, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83105974524609 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251090896161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_29 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83071685724277 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251094908777 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨29, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83071685724277 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251094908777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_30 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83037420903251 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562774731829 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨30, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83037420903251 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562774731829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_31 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83003180029973 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125551447563 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨31, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83003180029973 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125551447563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_32 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (1659379261461 / 2000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (281388366363 / 12500000000000 : ℝ))
      (E := (cell12704 ⟨32, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (1659379261461 / 2000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (281388366363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_33 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82934770001247 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (112555545949 / 5000000000000 : ℝ))
      (E := (cell12704 ⟨33, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82934770001247 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (112555545949 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_34 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82900600783487 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140694682443 / 6250000000000 : ℝ))
      (E := (cell12704 ⟨34, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82900600783487 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140694682443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_35 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20716613847213 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (11255594661 / 500000000000 : ℝ))
      (E := (cell12704 ⟨35, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20716613847213 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (11255594661 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_36 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82832333786581 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251122900407 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨36, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82832333786581 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251122900407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_37 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (8279823594607 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251126941517 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨37, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (8279823594607 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251126941517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_38 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (82764161836867 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251130938499 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨38, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (82764161836867 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251130938499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_39 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41365055714339 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125567475041 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨39, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41365055714339 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125567475041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12705_20 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41690571608643 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250936305589 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨20, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41690571608643 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250936305589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_21 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (10418332717237 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250940288811 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨21, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (10418332717237 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250940288811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_22 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (16662440899147 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (450188862711 / 20000000000000 : ℝ))
      (E := (cell12705 ⟨22, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (16662440899147 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (450188862711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_23 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41638885728963 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562737081321 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨23, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41638885728963 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562737081321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_24 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83243362591759 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125476163753 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨24, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83243362591759 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125476163753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_25 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83208977864693 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250956323493 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨25, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83208977864693 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250956323493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_26 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41587308622177 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250960316281 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨26, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41587308622177 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250960316281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_27 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83140280698533 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90038572347 / 4000000000000 : ℝ))
      (E := (cell12705 ⟨27, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83140280698533 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90038572347 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_28 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83105968195187 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125484151623 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨28, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83105968195187 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125484151623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_29 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20767919925609 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125486151167 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨29, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20767919925609 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125486151167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_30 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83037415188563 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250976308049 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨30, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83037415188563 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250976308049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_31 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41501587311007 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (225098032227 / 10000000000000 : ℝ))
      (E := (cell12705 ⟨31, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41501587311007 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (225098032227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_32 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82968957971393 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250984346651 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨32, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82968957971393 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250984346651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_33 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20733691301367 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250988324027 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨33, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20733691301367 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250988324027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_34 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41450298146581 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250992372743 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨34, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41450298146581 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250992372743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_35 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82866451203559 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250996376577 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨35, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82866451203559 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250996376577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_36 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82832329905897 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125500168103 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨36, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82832329905897 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125500168103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_37 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41399116184787 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251004369433 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨37, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41399116184787 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251004369433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_38 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82764158564139 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251008359229 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨38, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82764158564139 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2251008359229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_39 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (82730108459297 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125506182161 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨39, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (82730108459297 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125506182161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12706_20 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16676226882673 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281351723009 / 12500000000000 : ℝ))
      (E := (cell12706 ⟨20, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16676226882673 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281351723009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_21 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83346653244963 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250817748133 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨21, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83346653244963 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250817748133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_22 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83312196313357 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90032870177 / 4000000000000 : ℝ))
      (E := (cell12706 ⟨22, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83312196313357 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (90032870177 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_23 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (8327776358567 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250825806759 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨23, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (8327776358567 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250825806759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_24 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83243355029193 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250829791967 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨24, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83243355029193 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250829791967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_25 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83208970611387 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450166754329 / 20000000000000 : ℝ))
      (E := (cell12706 ⟨25, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83208970611387 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450166754329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_26 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83174610299877 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250837807251 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨26, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83174610299877 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250837807251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_27 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16628054812491 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250841784773 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨27, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16628054812491 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250841784773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_28 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (2077649046677 / 2500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125422882587 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨28, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (2077649046677 / 2500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125422882587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_29 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83071673681873 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125424904643 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨29, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83071673681873 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125424904643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_30 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83037409475117 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250853802261 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨30, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83037409475117 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250853802261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_31 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41501584607629 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562714451111 / 25000000000000 : ℝ))
      (E := (cell12706 ⟨31, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41501584607629 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562714451111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_32 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41484476435451 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250861817487 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨32, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41484476435451 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250861817487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_33 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41467380205409 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125432892113 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨33, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41467380205409 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125432892113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_34 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (8290059180393 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250869823003 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨34, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (8290059180393 / 10000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250869823003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_35 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (82866447019321 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125436908799 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨35, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (82866447019321 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125436908799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_36 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (10354040753279 / 12500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125438913669 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨36, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (10354040753279 / 12500000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125438913669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_37 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (4139911439703 / 5000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250881794067 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨37, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (4139911439703 / 5000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250881794067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_38 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16552831058471 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281360729427 / 12500000000000 : ℝ))
      (E := (cell12706 ⟨38, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16552831058471 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281360729427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_39 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (3309204219633 / 4000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (14068061463 / 625000000000 : ℝ))
      (E := (cell12706 ⟨39, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (3309204219633 / 4000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (14068061463 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12707_20 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41690562805529 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250691258627 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨20, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41690562805529 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250691258627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_21 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83346644753607 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250695261867 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨21, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83346644753607 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250695261867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_22 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83312188132519 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250699249767 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨22, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83312188132519 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250699249767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_23 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20819438928729 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250703284419 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨23, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20819438928729 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250703284419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_24 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20810836867023 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562676813163 / 25000000000000 : ℝ))
      (E := (cell12707 ⟨24, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20810836867023 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562676813163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_25 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83208963359507 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125355637229 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨25, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83208963359507 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125355637229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_26 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83174603356789 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562678823631 / 25000000000000 : ℝ))
      (E := (cell12707 ⟨26, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83174603356789 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562678823631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_27 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (8314026742773 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250719257209 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨27, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (8314026742773 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250719257209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_28 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83105955540289 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125361640973 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨28, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83105955540289 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125361640973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_29 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83071667662587 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450145462531 / 20000000000000 : ℝ))
      (E := (cell12707 ⟨29, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83071667662587 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (450145462531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_30 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (8303740376291 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (8791919113 / 390625000000 : ℝ))
      (E := (cell12707 ⟨30, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (8303740376291 / 10000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (8791919113 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_31 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16600632761941 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (225073528311 / 10000000000000 : ℝ))
      (E := (cell12707 ⟨31, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16600632761941 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (225073528311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_32 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41484473885789 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250739284853 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨32, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41484473885789 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250739284853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_33 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82934755617297 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250743299577 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨33, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82934755617297 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250743299577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_34 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82900587315789 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125373664239 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨34, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82900587315789 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125373664239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_35 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41433221418069 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125375656947 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨35, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41433221418069 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125375656947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_36 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (323563758389 / 390625000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125377657577 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨36, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (323563758389 / 390625000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125377657577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_37 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82798225219527 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250759332777 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨37, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82798225219527 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250759332777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_38 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20691038005379 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250763308361 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨38, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20691038005379 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250763308361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_39 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (82730102523261 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281345912579 / 12500000000000 : ℝ))
      (E := (cell12707 ⟨39, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (82730102523261 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281345912579 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12708_20 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83381116810367 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250568787531 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨20, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83381116810367 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250568787531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_21 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83346636263829 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250572830013 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨21, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83346636263829 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250572830013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_22 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (4165608997661 / 5000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450115359917 / 20000000000000 : ℝ))
      (E := (cell12708 ⟨22, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (4165608997661 / 5000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450115359917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_23 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (2602429620177 / 3125000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (281322602077 / 12500000000000 : ℝ))
      (E := (cell12708 ⟨23, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (2602429620177 / 3125000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (281322602077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_24 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (10405417488557 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562646206577 / 25000000000000 : ℝ))
      (E := (cell12708 ⟨24, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (10405417488557 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562646206577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_25 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16641791221811 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250588831931 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨25, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16641791221811 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250588831931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_26 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83174596415091 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250592836519 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨26, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83174596415091 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250592836519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_27 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20785065198589 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (18004774743 / 800000000000 : ℝ))
      (E := (cell12708 ⟨27, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20785065198589 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (18004774743 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_28 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20776487303703 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250600795099 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨28, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20776487303703 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250600795099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_29 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83071661644579 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250604812441 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨29, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83071661644579 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250604812441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_30 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (10379674756493 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562652209641 / 25000000000000 : ℝ))
      (E := (cell12708 ⟨30, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (10379674756493 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562652209641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_31 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16600631681071 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250612816807 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨31, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16600631681071 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250612816807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_32 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82968942673419 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (140663550457 / 6250000000000 : ℝ))
      (E := (cell12708 ⟨32, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82968942673419 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (140663550457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_33 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16586950164981 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125310405749 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨33, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16586950164981 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125310405749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_34 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (4145029141437 / 5000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (14066405191 / 625000000000 : ℝ))
      (E := (cell12708 ⟨34, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (4145029141437 / 5000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (14066405191 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_35 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (82866438654009 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250628865467 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨35, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (82866438654009 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250628865467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_36 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16566463653991 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250632858307 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨36, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16566463653991 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250632858307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_37 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (3311928865839 / 4000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (140664804263 / 6250000000000 : ℝ))
      (E := (cell12708 ⟨37, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (3311928865839 / 4000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (140664804263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_38 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41382074375811 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450128167353 / 20000000000000 : ℝ))
      (E := (cell12708 ⟨38, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41382074375811 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450128167353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_39 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20682524889151 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250644881431 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨39, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20682524889151 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250644881431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12709_20 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (8338110801129 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250446370787 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨20, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (8338110801129 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250446370787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_21 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83346627775627 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250450394271 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨21, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83346627775627 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250450394271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_22 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (4165608588773 / 5000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (140653396597 / 6250000000000 : ℝ))
      (E := (cell12709 ⟨22, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (4165608588773 / 5000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (140653396597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_23 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41638869988957 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450091669 / 20000000000 : ℝ))
      (E := (cell12709 ⟨23, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41638869988957 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450091669 / 20000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_24 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83243332350283 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225046239619 / 10000000000000 : ℝ))
      (E := (cell12709 ⟨24, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83243332350283 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225046239619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_25 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83208948860029 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562616596417 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨25, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83208948860029 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562616596417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_26 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83174589474781 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250470374817 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨26, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83174589474781 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250470374817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_27 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16628050832467 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562618591609 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨27, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16628050832467 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562618591609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_28 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83105942890649 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250478363097 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨28, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83105942890649 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250478363097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_29 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (10383956953481 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125241183567 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨29, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (10383956953481 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125241183567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_30 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41518696171109 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450097276131 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨30, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41518696171109 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450097276131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_31 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83003153002207 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450098081107 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨31, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83003153002207 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450098081107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_32 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (3318757503057 / 4000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250494384863 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨32, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (3318757503057 / 4000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250494384863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_33 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82934746033641 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250498378573 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨33, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82934746033641 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250498378573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_34 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82900578342783 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250502387857 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨34, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82900578342783 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250502387857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_35 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16573286894587 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450101282737 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨35, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16573286894587 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450101282737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_36 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82832314393343 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (35164224971 / 1562500000000 : ℝ))
      (E := (cell12709 ⟨36, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82832314393343 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (35164224971 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_37 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82798218073403 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250514400361 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨37, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82798218073403 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250514400361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_38 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (82764145482671 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225051842063 / 10000000000000 : ℝ))
      (E := (cell12709 ⟨38, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (82764145482671 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225051842063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_39 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41365048295427 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125261200151 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨39, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41365048295427 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125261200151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12710_20 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83381099213827 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562580987529 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨20, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83381099213827 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562580987529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_21 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41673309644501 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250327954639 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨21, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41673309644501 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250327954639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_22 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83312163599239 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562582986499 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨22, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83312163599239 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562582986499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_23 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16655546422333 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250335986273 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨23, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16655546422333 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250335986273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_24 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41621662396787 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250339962301 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨24, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41621662396787 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250339962301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_25 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83208941612429 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562585998517 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨25, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83208941612429 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562585998517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_26 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (4158729126793 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250347967839 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨26, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (4158729126793 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250347967839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_27 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (5196265470729 / 6250000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250352003229 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨27, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (5196265470729 / 6250000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250352003229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_28 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (415529682839 / 500000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250355985943 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨28, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (415529682839 / 500000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250355985943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_29 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83071649612393 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125179988369 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨29, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83071649612393 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125179988369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_30 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83037386633731 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250363977717 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨30, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83037386633731 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250363977717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_31 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41501573800131 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250367990759 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨31, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41501573800131 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250367990759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_32 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82968932480597 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250372017509 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨32, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82968932480597 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250372017509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_33 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16586948248701 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250376000803 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨33, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16586948248701 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250376000803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_34 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20725143464479 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562595000093 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨34, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20725143464479 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562595000093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_35 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20716607573229 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250384017181 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨35, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20716607573229 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250384017181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_36 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20708077629437 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (56259699833 / 2500000000000 : ℝ))
      (E := (cell12710 ⟨36, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20708077629437 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (56259699833 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_37 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20699553625453 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125195993957 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨37, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20699553625453 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125195993957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_38 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82764142214663 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250396001257 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨38, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82764142214663 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250396001257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_39 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (82730093626011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (112520001671 / 5000000000000 : ℝ))
      (E := (cell12710 ⟨39, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (82730093626011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (112520001671 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12711_20 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41690545208989 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250201583799 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨20, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41690545208989 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250201583799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_21 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83346610803953 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250205627727 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨21, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83346610803953 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250205627727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_22 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83312155424557 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250209600917 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨22, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83312155424557 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250209600917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_23 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83277724246917 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281276702967 / 12500000000000 : ℝ))
      (E := (cell12711 ⟨23, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83277724246917 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281276702967 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_24 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (10405414654791 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250217583013 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨24, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (10405414654791 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250217583013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_25 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16641786873251 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450044319747 / 20000000000000 : ℝ))
      (E := (cell12711 ⟨25, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16641786873251 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450044319747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_26 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (10396821949791 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125112807793 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨26, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (10396821949791 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125112807793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_27 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (10392530112793 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450045927273 / 20000000000000 : ℝ))
      (E := (cell12711 ⟨27, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (10392530112793 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450045927273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_28 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16621186049253 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562558401293 / 25000000000000 : ℝ))
      (E := (cell12711 ⟨28, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16621186049253 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562558401293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_29 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16614328719643 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562559410313 / 25000000000000 : ℝ))
      (E := (cell12711 ⟨29, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16614328719643 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562559410313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_30 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83037380926483 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250241629753 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨30, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83037380926483 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250241629753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_31 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83003142199519 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281280703877 / 12500000000000 : ℝ))
      (E := (cell12711 ⟨31, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83003142199519 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281280703877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_32 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82968927385933 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (225024964669 / 10000000000000 : ℝ))
      (E := (cell12711 ⟨32, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82968927385933 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (225024964669 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_33 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82934736454497 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125126809803 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨33, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82934736454497 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125126809803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_34 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (4145028468707 / 5000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250257609497 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨34, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (4145028468707 / 5000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250257609497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_35 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (1657328522279 / 2000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125130808663 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨35, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (1657328522279 / 2000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125130808663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_36 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (8283230664317 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250265643837 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨36, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (8283230664317 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250265643837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_37 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (82798210931201 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250269630869 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨37, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (82798210931201 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250269630869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_38 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (206910347369 / 250000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (70321051167 / 3125000000000 : ℝ))
      (E := (cell12711 ⟨38, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (206910347369 / 250000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (70321051167 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_39 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41365045331037 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250277663339 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨39, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41365045331037 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250277663339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12712_20 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41690540811871 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250079271837 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨20, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41690540811871 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250079271837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_21 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83346602320479 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125041619313 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨21, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83346602320479 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125041619313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_22 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (20828036812853 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250087251991 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨22, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (20828036812853 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250087251991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_23 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (20819429095917 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250091257391 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨23, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (20819429095917 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250091257391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_24 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (16648661936909 / 20000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250095258327 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨24, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (16648661936909 / 20000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250095258327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_25 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41604463560753 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250099258067 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨25, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41604463560753 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250099258067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_26 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83174568662183 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (56252581491 / 2500000000000 : ℝ))
      (E := (cell12712 ⟨26, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83174568662183 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (56252581491 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_27 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (133024374839 / 160000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125053632923 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨27, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (133024374839 / 160000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125053632923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_28 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41552961963021 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (9000445117 / 400000000000 : ℝ))
      (E := (cell12712 ⟨28, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41552961963021 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (9000445117 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_29 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (2595988674541 / 3125000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250115302187 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨29, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (2595988674541 / 3125000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250115302187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_30 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41518687610237 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125059639123 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨30, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41518687610237 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125059639123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_31 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83003136799977 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (225012326777 / 10000000000000 : ℝ))
      (E := (cell12712 ⟨31, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83003136799977 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (225012326777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_32 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41484461146217 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562531818101 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨32, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41484461146217 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562531818101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_33 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82934731666617 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125065646783 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨33, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82934731666617 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125065646783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_34 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (16580112978291 / 20000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250135273839 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨34, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (16580112978291 / 20000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250135273839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_35 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82866421936037 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125069665691 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨35, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82866421936037 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125069665691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_36 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82832302769609 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (14063395569 / 625000000000 : ℝ))
      (E := (cell12712 ⟨36, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82832302769609 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (14063395569 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_37 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (8279820736157 / 10000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125073664613 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨37, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (8279820736157 / 10000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125073664613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_38 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (82764135681479 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (17579307257 / 781250000000 : ℝ))
      (E := (cell12712 ⟨38, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (82764135681479 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (17579307257 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_39 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (20682521924761 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250155348781 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨39, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (20682521924761 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250155348781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12713_20 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83381072831119 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249956955951 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨20, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83381072831119 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249956955951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_21 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83346593838581 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (449992192449 / 20000000000000 : ℝ))
      (E := (cell12713 ⟨21, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83346593838581 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (449992192449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_22 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16662427815961 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281245619693 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨22, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16662427815961 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281245619693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_23 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (260242839131 / 312500000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249968945587 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨23, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (260242839131 / 312500000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249968945587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_24 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (162584574477 / 195312500000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124986494123 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨24, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (162584574477 / 195312500000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124986494123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_25 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41604459939091 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (70311780377 / 3125000000000 : ℝ))
      (E := (cell12713 ⟨25, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41604459939091 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (70311780377 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_26 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41587280863713 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124990479211 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨26, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41587280863713 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124990479211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_27 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20785056911939 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249985008559 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨27, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20785056911939 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249985008559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_28 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83105917607133 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249989008179 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨28, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83105917607133 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249989008179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_29 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16614326314737 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281249119943 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨29, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16614326314737 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281249119943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_30 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83037369515703 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124998490857 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨30, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83037369515703 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124998490857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_31 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83003131401637 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250001018097 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨31, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83003131401637 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250001018097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_32 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82968917200099 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125002505889 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨32, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82968917200099 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125002505889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_33 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (10366840859983 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562502255671 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨33, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (10366840859983 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562502255671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_34 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (4145028020493 / 5000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125006496701 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨34, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (4145028020493 / 5000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125006496701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_35 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41433208879589 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (70313030733 / 3125000000000 : ℝ))
      (E := (cell12713 ⟨35, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41433208879589 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (70313030733 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_36 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (10354037362133 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125010496793 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨36, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (10354037362133 / 12500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1125010496793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_37 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82798203792919 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562506256077 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨37, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82798203792919 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562506256077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_38 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (82764132416301 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250029017211 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨38, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (82764132416301 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2250029017211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_39 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (2068252118423 / 2500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140627064439 / 6250000000000 : ℝ))
      (E := (cell12713 ⟨39, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (2068252118423 / 2500000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (140627064439 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12714_20 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (20845266010027 / 25000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249834694423 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨20, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (20845266010027 / 25000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249834694423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_21 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83346585358257 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249838681981 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨21, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83346585358257 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249838681981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_22 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16662426181947 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (112492135879 / 5000000000000 : ℝ))
      (E := (cell12714 ⟨22, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16662426181947 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (112492135879 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_23 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (10409712582709 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124923344163 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨23, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (10409712582709 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124923344163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_24 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16648658916273 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249850714397 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨24, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16648658916273 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249850714397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_25 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83208912636283 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249854682331 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨25, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83208912636283 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249854682331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_26 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (10396819349257 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562464677983 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨26, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (10396819349257 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562464677983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_27 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41570110511243 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281232836147 / 12500000000000 : ℝ))
      (E := (cell12714 ⟨27, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41570110511243 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (281232836147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_28 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (1298529863899 / 1562500000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124933366747 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨28, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (1298529863899 / 1562500000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124933366747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_29 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41535812781667 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449974146061 / 20000000000000 : ℝ))
      (E := (cell12714 ⟨29, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41535812781667 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449974146061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_30 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (8303736381217 / 10000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124937370079 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨30, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (8303736381217 / 10000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124937370079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_31 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83003126004497 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249878706387 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨31, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83003126004497 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249878706387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_32 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (648194625851 / 781250000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249882747689 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨32, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (648194625851 / 781250000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249882747689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_33 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82934722094237 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249886748379 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨33, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82934722094237 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249886748379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_34 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16580111185871 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249890709579 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨34, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16580111185871 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249890709579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_35 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (20716603395843 / 25000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449978949889 / 20000000000000 : ℝ))
      (E := (cell12714 ⟨35, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (20716603395843 / 25000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449978949889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_36 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16566459005107 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562474687869 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨36, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16566459005107 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562474687869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_37 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (82798200225247 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449980554959 / 20000000000000 : ℝ))
      (E := (cell12714 ⟨37, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (82798200225247 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449980554959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_38 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16552825830413 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249906760993 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨38, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16552825830413 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249906760993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_39 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41365040887851 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124955384397 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨39, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41365040887851 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124955384397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12715_20 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (8338105525071 / 10000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562428121813 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨20, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (8338105525071 / 10000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562428121813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_21 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20836644219877 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249716456137 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨21, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20836644219877 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249716456137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_22 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41656061370601 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249720473771 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨22, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41656061370601 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249720473771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_23 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41638846401461 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249724485611 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨23, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41638846401461 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249724485611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_24 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (2601352719749 / 3125000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124864247577 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨24, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (2601352719749 / 3125000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124864247577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_25 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83208905395807 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449946501133 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨25, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83208905395807 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449946501133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_26 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83174547862073 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281217057719 / 12500000000000 : ℝ))
      (E := (cell12715 ⟨26, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83174547862073 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281217057719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_27 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41570107199283 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249740483029 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨27, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41570107199283 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249740483029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_28 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20776476243313 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249744513661 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨28, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20776476243313 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249744513661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_29 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83071619554257 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562437124373 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨29, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83071619554257 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562437124373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_30 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (664298864879 / 800000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281219061883 / 12500000000000 : ℝ))
      (E := (cell12715 ⟨30, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (664298864879 / 800000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281219061883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_31 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41501560304279 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249756508253 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨31, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41501560304279 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249756508253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_32 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82968907018921 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249760480137 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨32, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82968907018921 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249760480137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_33 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82934717309737 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124882264617 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨33, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82934717309737 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124882264617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_34 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (82900551449939 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124884240489 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨34, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (82900551449939 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124884240489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_35 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41433204704309 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449954502417 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨35, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41433204704309 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449954502417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_36 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41416145577511 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449955301211 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨36, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41416145577511 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449955301211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_37 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41399098329277 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224978052201 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨37, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41399098329277 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224978052201 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_38 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (20691031472193 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249784501539 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨38, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (20691031472193 / 25000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249784501539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_39 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (8273007881539 / 10000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124894251683 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨39, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (8273007881539 / 10000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124894251683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12716_20 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83381046462923 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249590276161 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨20, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83381046462923 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249590276161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_21 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83346568402333 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124797142357 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨21, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83346568402333 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124797142357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_22 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16662422914841 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124799142223 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨22, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16662422914841 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124799142223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_23 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (10409710618209 / 12500000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249602279089 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨23, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (10409710618209 / 12500000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249602279089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_24 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83243279484033 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140600392009 / 6250000000000 : ℝ))
      (E := (cell12716 ⟨24, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83243279484033 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140600392009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_25 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (20802224539189 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281201283359 / 12500000000000 : ℝ))
      (E := (cell12716 ⟨25, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (20802224539189 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281201283359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_26 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83174540931477 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249614266301 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨26, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83174540931477 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249614266301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_27 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (20785051943999 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562404568307 / 25000000000000 : ℝ))
      (E := (cell12716 ⟨27, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (20785051943999 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562404568307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_28 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83105898658279 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449924458043 / 20000000000000 : ℝ))
      (E := (cell12716 ⟨28, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83105898658279 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449924458043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_29 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16614322709291 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249626319593 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨29, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16614322709291 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249626319593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_30 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41518676204409 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249630304947 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨30, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41518676204409 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249630304947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_31 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (4150155760691 / 5000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124817153309 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨31, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (4150155760691 / 5000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124817153309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_32 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82968901930077 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249638326247 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨32, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82968901930077 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249638326247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_33 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82934712526363 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124821153333 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨33, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82934712526363 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124821153333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_34 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82900546971613 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124823153799 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨34, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82900546971613 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124823153799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_35 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82866405234917 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249650330009 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨35, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82866405234917 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249650330009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_36 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (3313291491421 / 4000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249654315979 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨36, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (3313291491421 / 4000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249654315979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_37 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82798193092839 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249658324631 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨37, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82798193092839 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249658324631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_38 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (82764122626421 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140603893597 / 6250000000000 : ℝ))
      (E := (cell12716 ⟨38, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (82764122626421 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140603893597 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_39 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41365037927991 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249666352193 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨39, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41365037927991 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249666352193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12717_20 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (20845259419187 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (224946811943 / 10000000000000 : ℝ))
      (E := (cell12717 ⟨20, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (20845259419187 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (224946811943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_21 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83346559926731 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249472109411 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨21, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83346559926731 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249472109411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_22 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10414013301093 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124738045639 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨22, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10414013301093 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124738045639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_23 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (130121370453 / 156250000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124740063557 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨23, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (130121370453 / 156250000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124740063557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_24 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41621635968779 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124742051871 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨24, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41621635968779 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124742051871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_25 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10401111364891 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249488141147 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨25, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10401111364891 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249488141147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_26 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41587267001133 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (140593257849 / 6250000000000 : ℝ))
      (E := (cell12717 ⟨26, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41587267001133 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (140593257849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_27 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41570100577387 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124748059111 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨27, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41570100577387 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124748059111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_28 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83105892344617 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (17996000973 / 800000000000 : ℝ))
      (E := (cell12717 ⟨28, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83105892344617 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (17996000973 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_29 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83071607539927 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (56237603453 / 2500000000000 : ℝ))
      (E := (cell12717 ⟨29, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83071607539927 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (56237603453 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_30 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83037346708997 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124754055647 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨30, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83037346708997 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124754055647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_31 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83003109820281 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (281189020003 / 12500000000000 : ℝ))
      (E := (cell12717 ⟨31, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83003109820281 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (281189020003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_32 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (16593779368479 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (4393586153 / 195312500000 : ℝ))
      (E := (cell12717 ⟨32, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (16593779368479 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (4393586153 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_33 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (16586941548823 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (112476006963 / 5000000000000 : ℝ))
      (E := (cell12717 ⟨33, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (16586941548823 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (112476006963 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_34 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10362567811797 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449904826167 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨34, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10362567811797 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449904826167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_35 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (20716600265567 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249528144587 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨35, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (20716600265567 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249528144587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_36 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41416141708521 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (359925149 / 16000000000 : ℝ))
      (E := (cell12717 ⟨36, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41416141708521 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (359925149 / 16000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_37 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82798189528103 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (112476809133 / 5000000000000 : ℝ))
      (E := (cell12717 ⟨37, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82798189528103 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (112476809133 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_38 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (82764119365011 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124770074517 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨38, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (82764119365011 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124770074517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_39 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (2068251822437 / 2500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249544139097 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨39, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (2068251822437 / 2500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249544139097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12718_20 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83381028892183 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124672979391 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨20, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83381028892183 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124672979391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_21 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83346551452703 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249349988531 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨21, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83346551452703 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249349988531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_22 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83312098244819 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562338488149 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨22, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83312098244819 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562338488149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_23 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41638834617833 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249357971337 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨23, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41638834617833 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249357971337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_24 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (2601352012267 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (44987239799 / 2000000000000 : ℝ))
      (E := (cell12718 ⟨24, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (2601352012267 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (44987239799 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_25 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83208883682923 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (140585375731 / 6250000000000 : ℝ))
      (E := (cell12718 ⟨25, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83208883682923 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (140585375731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_26 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83174527074441 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249369981179 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨26, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83174527074441 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249369981179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_27 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (831401945349 / 1000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562343504503 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨27, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (831401945349 / 1000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562343504503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_28 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83105886032267 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249378007891 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨28, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83105886032267 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249378007891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_29 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41535800767337 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (449876402313 / 20000000000000 : ℝ))
      (E := (cell12718 ⟨29, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41535800767337 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (449876402313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_30 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83037341010413 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249385972621 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨30, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83037341010413 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249385972621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_31 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41501552213971 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249390009933 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨31, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41501552213971 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249390009933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_32 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82968891755877 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249394008089 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨32, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82968891755877 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249394008089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_33 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82934702962993 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124699013509 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨33, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82934702962993 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124699013509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_34 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82900538018227 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124701004649 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨34, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82900538018227 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124701004649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_35 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82866396890671 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249406014451 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨35, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82866396890671 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249406014451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_36 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (3313291181983 / 4000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249410043213 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨36, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (3313291181983 / 4000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249410043213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_37 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (16559637192869 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249414037419 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨37, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (16559637192869 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249414037419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_38 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82764116104543 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249418055987 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨38, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82764116104543 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249418055987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_39 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (82730069939883 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249422040259 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨39, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (82730069939883 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249422040259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12719_20 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83381020109229 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140576490781 / 6250000000000 : ℝ))
      (E := (cell12719 ⟨20, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83381020109229 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140576490781 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_21 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83346542980247 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249227863773 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨21, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83346542980247 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249227863773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_22 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83312090082429 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249231868401 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨22, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83312090082429 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249231868401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_23 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83277661382909 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249235870109 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨23, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83277661382909 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249235870109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_24 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (8324325684899 / 10000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449847974479 / 20000000000000 : ℝ))
      (E := (cell12719 ⟨24, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (8324325684899 / 10000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449847974479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_25 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83208876448141 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (56231096963 / 2500000000000 : ℝ))
      (E := (cell12719 ⟨25, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83208876448141 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (56231096963 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_26 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41587260074001 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562311972877 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨26, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41587260074001 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562311972877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_27 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (665121503331 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (281156489269 / 12500000000000 : ℝ))
      (E := (cell12719 ⟨27, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (665121503331 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (281156489269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_28 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (20776469930307 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124627945273 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨28, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (20776469930307 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124627945273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_29 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83071595530693 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249259881439 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨29, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83071595530693 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249259881439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_30 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41518667656533 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (70289496529 / 3125000000000 : ℝ))
      (E := (cell12719 ⟨30, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41518667656533 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (70289496529 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_31 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83003099036803 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249267914883 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨31, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83003099036803 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249267914883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_32 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (2074222166763 / 2500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140579493899 / 6250000000000 : ℝ))
      (E := (cell12719 ⟨32, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (2074222166763 / 2500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140579493899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_33 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (20733674545749 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562318977839 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨33, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (20733674545749 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562318977839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_34 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (82900533543167 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124639971493 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨34, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (82900533543167 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124639971493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_35 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (662931141761 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249283939603 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨35, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (662931141761 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249283939603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_36 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41416137841561 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224928790187 / 10000000000000 : ℝ))
      (E := (cell12719 ⟨36, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41416137841561 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224928790187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_37 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (16559636480313 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249291947587 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨37, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (16559636480313 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249291947587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_38 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (10345514105627 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249295959707 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨38, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (10345514105627 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249295959707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_39 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (8273006698319 / 10000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249299938227 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨39, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (8273006698319 / 10000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249299938227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12720_20 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (16676202265577 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89964072023 / 4000000000000 : ℝ))
      (E := (cell12720 ⟨20, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (16676202265577 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89964072023 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_21 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (20836633627341 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124552896721 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨21, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (20836633627341 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124552896721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_22 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41656040960787 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124554919347 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨22, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41656040960787 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124554919347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_23 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (1665553070633 / 2000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249113823431 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨23, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (1665553070633 / 2000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249113823431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_24 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (16648649861379 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249117809453 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨24, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (16648649861379 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249117809453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_25 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41604434607391 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124560900009 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨25, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41604434607391 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124560900009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_26 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83174513222947 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249125856573 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨26, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83174513222947 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249125856573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_27 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83140181299197 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124564903323 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨27, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83140181299197 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124564903323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_28 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83105873411499 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249133828061 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨28, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83105873411499 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249133828061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_29 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41535794763993 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562284466181 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨29, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41535794763993 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562284466181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_30 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (16607465923391 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249141860217 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨30, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (16607465923391 / 20000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249141860217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_31 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41501546823431 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112457290817 / 5000000000000 : ℝ))
      (E := (cell12720 ⟨31, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41501546823431 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112457290817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_32 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41484440793163 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249149851783 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨32, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41484440793163 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249149851783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_33 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (20733673351031 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249153850861 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨33, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (20733673351031 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249153850861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_34 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41450264534597 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124578936647 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨34, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41450264534597 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124578936647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_35 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (8286638855063 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249161861411 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨35, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (8286638855063 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249161861411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_36 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (20708067954421 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562291468633 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨36, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (20708067954421 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562291468633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_37 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82798178839763 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281146231811 / 12500000000000 : ℝ))
      (E := (cell12720 ⟨37, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82798178839763 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (281146231811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_38 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (8276410958643 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124586930099 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨38, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (8276410958643 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124586930099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_39 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (82730064027401 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (140573618233 / 6250000000000 : ℝ))
      (E := (cell12720 ⟨39, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (82730064027401 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (140573618233 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12721_20 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (1667620050963 / 2000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124489901509 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨20, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (1667620050963 / 2000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124489901509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_21 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83346526040053 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (8785092881 / 390625000000 : ℝ))
      (E := (cell12721 ⟨21, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83346526040053 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (8785092881 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_22 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83312073762253 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562246951287 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨22, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83312073762253 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562246951287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_23 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (2602426427559 / 3125000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281123971619 / 12500000000000 : ℝ))
      (E := (cell12721 ⟨23, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (2602426427559 / 3125000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281123971619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_24 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83243241766261 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248995801121 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨24, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83243241766261 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248995801121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_25 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (20802215495711 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224899977619 / 10000000000000 : ℝ))
      (E := (cell12721 ⟨25, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (20802215495711 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (224899977619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_26 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41587253149639 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (70281369311 / 3125000000000 : ℝ))
      (E := (cell12721 ⟨26, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41587253149639 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (70281369311 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_27 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41570087341683 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124503906191 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨27, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41570087341683 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124503906191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_28 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (2077646677577 / 2500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124505910217 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨28, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (2077646677577 / 2500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124505910217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_29 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (10383947940819 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249015785947 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨29, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (10383947940819 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249015785947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_30 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83037323922079 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124509913987 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨30, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83037323922079 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124509913987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_31 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (2075077206453 / 2500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124511915689 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨31, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (2075077206453 / 2500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124511915689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_32 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82968876503293 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124513898863 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨32, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82968876503293 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124513898863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_33 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82934688626377 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249031845531 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨33, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82934688626377 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249031845531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_34 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (8290052459631 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249035800219 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨34, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (8290052459631 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249035800219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_35 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41433192191093 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562259959627 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨35, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41433192191093 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562259959627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_36 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (4141613397663 / 5000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (140565240243 / 6250000000000 : ℝ))
      (E := (cell12721 ⟨36, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (4141613397663 / 5000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (140565240243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_37 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41399087639469 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249047816799 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨37, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41399087639469 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2249047816799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_38 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (16552821265757 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (14056573851 / 625000000000 : ℝ))
      (E := (cell12721 ⟨38, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (16552821265757 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (14056573851 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_39 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (82730061072517 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449811168407 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨39, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (82730061072517 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449811168407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12722_20 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (3335239750801 / 4000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562214450387 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨20, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (3335239750801 / 4000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562214450387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_21 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83346517572313 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112443090803 / 5000000000000 : ℝ))
      (E := (cell12722 ⟨21, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83346517572313 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112443090803 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_22 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41656032802233 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248865767767 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨22, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41656032802233 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248865767767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_23 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41638818916811 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248869777027 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨23, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41638818916811 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248869777027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_24 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (16648646845417 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281109223629 / 12500000000000 : ℝ))
      (E := (cell12722 ⟨24, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (16648646845417 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281109223629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_25 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (10401106844041 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124438903519 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨25, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (10401106844041 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124438903519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_26 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (2599203105531 / 3125000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248881775649 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨26, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (2599203105531 / 3125000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248881775649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_27 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83140168068883 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248885814473 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨27, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83140168068883 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248885814473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_28 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83105860795971 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124444904601 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨28, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83105860795971 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124444904601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_29 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8307157752639 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449778764117 / 20000000000000 : ℝ))
      (E := (cell12722 ⟨29, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8307157752639 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449778764117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_30 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83037318228439 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248897792201 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨30, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83037318228439 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248897792201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_31 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (5187692679411 / 6250000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562225460731 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨31, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (5187692679411 / 6250000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562225460731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_32 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82968871421421 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248905798777 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨32, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82968871421421 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248905798777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_33 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41467341924877 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449781967357 / 20000000000000 : ℝ))
      (E := (cell12722 ⟨33, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41467341924877 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449781967357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_34 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (2590641253891 / 3125000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124456920493 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨34, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (2590641253891 / 3125000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124456920493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_35 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82866380214793 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449783562453 / 20000000000000 : ℝ))
      (E := (cell12722 ⟨35, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82866380214793 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (449783562453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_36 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82832264089849 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124460904971 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨36, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82832264089849 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124460904971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_37 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8279817171909 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (89957033381 / 4000000000000 : ℝ))
      (E := (cell12722 ⟨37, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8279817171909 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (89957033381 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_38 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (82764103072079 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124464913799 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨38, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (82764103072079 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124464913799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_39 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (10341257264817 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248933847879 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨39, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (10341257264817 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248933847879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12723_20 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20845246248377 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562183949041 / 25000000000000 : ℝ))
      (E := (cell12723 ⟨20, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20845246248377 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562183949041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_21 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (2604578409567 / 3125000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248739850709 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨21, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (2604578409567 / 3125000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248739850709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_22 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83312057448213 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248743843203 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨22, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83312057448213 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248743843203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_23 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20819407496713 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124373917827 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨23, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20819407496713 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124373917827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_24 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83243226689367 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562187957889 / 25000000000000 : ℝ))
      (E := (cell12723 ⟨24, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83243226689367 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562187957889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_25 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83208847523233 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449751166833 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨25, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83208847523233 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449751166833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_26 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (8317449245609 / 10000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449751969301 / 20000000000000 : ℝ))
      (E := (cell12723 ⟨26, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (8317449245609 / 10000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (449751969301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_27 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41570080727873 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124381906459 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨27, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41570080727873 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124381906459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_28 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83105854490171 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (224876785283 / 10000000000000 : ℝ))
      (E := (cell12723 ⟨28, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83105854490171 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (224876785283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_29 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83071571527501 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248771851653 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨29, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83071571527501 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248771851653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_30 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41518656268017 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124387934963 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨30, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41518656268017 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124387934963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_31 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83003077484231 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (70274370343 / 3125000000000 : ℝ))
      (E := (cell12723 ⟨31, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83003077484231 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (70274370343 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_32 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82968866340711 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124391927467 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨32, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82968866340711 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124391927467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_33 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16586935814851 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (281098485401 / 12500000000000 : ℝ))
      (E := (cell12723 ⟨33, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16586935814851 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (281098485401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_34 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41450257826901 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562197969593 / 25000000000000 : ℝ))
      (E := (cell12723 ⟨34, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41450257826901 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562197969593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_35 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (1657327520969 / 2000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (70274870041 / 3125000000000 : ℝ))
      (E := (cell12723 ⟨35, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (1657327520969 / 2000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (70274870041 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_36 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20708065056863 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124399945001 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨36, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20708065056863 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124399945001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_37 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (82798168160219 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248803848983 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨37, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (82798168160219 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248803848983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_38 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41382049908157 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248807894509 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨38, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41382049908157 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248807894509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_39 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41365027582729 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124405954629 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨39, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41365027582729 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124405954629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12724_20 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (416904881093 / 500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (224861390343 / 10000000000000 : ℝ))
      (E := (cell12724 ⟨20, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (416904881093 / 500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (224861390343 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_21 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83346500641547 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562154470371 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨21, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83346500641547 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562154470371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_22 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83312049293493 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562155478701 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨22, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83312049293493 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562155478701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_23 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41638811070789 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449725178097 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨23, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41638811070789 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449725178097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_24 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83243219153109 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (281078741087 / 12500000000000 : ℝ))
      (E := (cell12724 ⟨24, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83243219153109 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (281078741087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_25 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83208840295559 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248633915971 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨25, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83208840295559 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248633915971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_26 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (20793621384143 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248637913679 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨26, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (20793621384143 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248637913679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_27 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16628030968791 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248641924611 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨27, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16628030968791 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248641924611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_28 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (1038823102321 / 1250000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124322946427 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨28, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (1038823102321 / 1250000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124322946427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_29 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83071565529883 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248649937647 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨29, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83071565529883 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248649937647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_30 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (1297457919451 / 1562500000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248653944123 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨30, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (1297457919451 / 1562500000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248653944123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_31 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83003072099083 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248657914077 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨31, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83003072099083 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248657914077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_32 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82968861261161 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124330953819 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨32, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82968861261161 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124330953819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_33 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (2073366857497 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449733185243 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨33, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (2073366857497 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449733185243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_34 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82900511184179 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (112433495619 / 5000000000000 : ℝ))
      (E := (cell12724 ⟨34, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82900511184179 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (112433495619 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_35 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82866371883157 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248673925651 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨35, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82866371883157 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248673925651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_36 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82832256366069 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248677966761 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨36, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82832256366069 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248677966761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_37 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (20699541150581 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124340959429 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨37, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (20699541150581 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124340959429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_38 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (82764096561489 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248685958193 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨38, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (82764096561489 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248685958193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_39 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (20682513053321 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248689967447 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨39, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (20682513053321 / 25000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248689967447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

end BstLean.Part268
