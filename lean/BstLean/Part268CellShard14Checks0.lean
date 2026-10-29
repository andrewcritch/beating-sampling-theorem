import BstLean.Part268CellShard14Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12700_0 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (42037995208089 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225146947347 / 10000000000000 : ℝ))
      (E := (cell12700 ⟨0, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (42037995208089 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225146947347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_1 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (10505126927221 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251473507023 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨1, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (10505126927221 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251473507023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_2 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (84006065353633 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225147750839 / 10000000000000 : ℝ))
      (E := (cell12700 ⟨2, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (84006065353633 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (225147750839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_3 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (10496392523409 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125740743207 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨3, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (10496392523409 / 12500000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125740743207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_4 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (671489919059 / 800000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251485507583 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨4, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (671489919059 / 800000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251485507583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_5 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (3356054576113 / 4000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251489522367 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨5, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (3356054576113 / 4000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251489522367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_6 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20966628428173 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125746740443 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨6, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20966628428173 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125746740443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_7 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83831687776237 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251497506833 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨7, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83831687776237 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251497506833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_8 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20949221639477 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562875372961 / 25000000000000 : ℝ))
      (E := (cell12700 ⟨8, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20949221639477 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562875372961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_9 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83762110022337 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125752750591 / 50000000000000 : ℝ))
      (E := (cell12700 ⟨9, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83762110022337 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (1125752750591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_10 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16745471626869 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251509483857 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨10, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16745471626869 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251509483857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_11 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20923157714733 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562878376169 / 25000000000000 : ℝ))
      (E := (cell12700 ⟨11, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20923157714733 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (562878376169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_12 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (16731585632257 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251517512103 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨12, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (16731585632257 / 20000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251517512103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_13 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (5226453125423 / 6250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251521512381 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨13, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (5226453125423 / 6250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251521512381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_14 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83588596360929 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251525511501 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨14, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83588596360929 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251525511501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_15 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (41776983594747 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281441189401 / 12500000000000 : ℝ))
      (E := (cell12700 ⟨15, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (41776983594747 / 50000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (281441189401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_16 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20879840614591 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (140720845563 / 6250000000000 : ℝ))
      (E := (cell12700 ⟨16, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20879840614591 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (140720845563 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_17 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (83484782133621 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251537499947 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨17, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (83484782133621 / 100000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251537499947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_18 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (1043127827269 / 1250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450308298241 / 20000000000000 : ℝ))
      (E := (cell12700 ⟨18, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (1043127827269 / 1250000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (450308298241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12700_19 : CellCertificate 12700 (6927269902277 / 78125000000000 : ℝ) (826946011944211 / 500000000000000000 : ℝ) (334078402304341 / 10000000000000000 : ℝ)
    (cell12700 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · norm_num [cell12700]
  · have h := gap_lower (n := 12700) (a := (20853923642123 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251545507553 / 100000000000000 : ℝ))
      (E := (cell12700 ⟨19, by decide⟩).energy) (xi := (334078402304341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12700 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12700]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12700])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12700) (a := (20853923642123 / 25000000000000 : ℝ)) (b := (162189352327 / 100000000000000 : ℝ)) (q := (2251545507553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12700])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12700]

theorem cert12701_0 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (84075975288101 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450269363061 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨0, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (84075975288101 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450269363061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_1 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (4202050030487 / 5000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (17588678241 / 781250000000 : ℝ))
      (E := (cell12701 ⟨1, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (4202050030487 / 5000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (17588678241 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_2 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (84006050865201 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125677391467 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨2, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (84006050865201 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125677391467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_3 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (1312048844031 / 1562500000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450271757257 / 20000000000000 : ℝ))
      (E := (cell12701 ⟨3, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (1312048844031 / 1562500000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (450271757257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_4 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83936226031781 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (70355086739 / 3125000000000 : ℝ))
      (E := (cell12701 ⟨4, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83936226031781 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (70355086739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_5 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41950675435237 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251366817279 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨5, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41950675435237 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251366817279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_6 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83866500498137 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125685401707 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨6, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83866500498137 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125685401707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_7 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (8383167487903 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562843699943 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨7, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (8383167487903 / 10000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562843699943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_8 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83796873977601 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562844703479 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨8, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83796873977601 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562844703479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_9 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (16752419551697 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562845698783 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨9, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (16752419551697 / 20000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562845698783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_10 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83727346186503 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251386808449 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨10, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83727346186503 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251386808449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_11 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (2615394350833 / 3125000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140711925163 / 6250000000000 : ℝ))
      (E := (cell12701 ⟨11, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (2615394350833 / 3125000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (140711925163 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_12 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (20914479211033 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125697392047 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨12, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (20914479211033 / 25000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125697392047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_13 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83623239004297 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251398817261 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨13, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83623239004297 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251398817261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_14 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41794292836349 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281425348987 / 12500000000000 : ℝ))
      (E := (cell12701 ⟨14, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41794292836349 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281425348987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_15 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (41776978407531 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125703385917 / 50000000000000 : ℝ))
      (E := (cell12701 ⟨15, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (41776978407531 / 50000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (1125703385917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_16 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (83519352397293 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251410820763 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨16, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (83519352397293 / 100000000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251410820763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_17 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (1304449568523 / 1562500000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281426846173 / 12500000000000 : ℝ))
      (E := (cell12701 ⟨17, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (1304449568523 / 1562500000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (281426846173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_18 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (651954818327 / 781250000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562854699317 / 25000000000000 : ℝ))
      (E := (cell12701 ⟨18, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (651954818327 / 781250000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (562854699317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12701_19 : CellCertificate 12701 (177332522573531 / 2000000000000000 : ℝ) (413440440903097 / 250000000000000000 : ℝ) (334051457338871 / 10000000000000000 : ℝ)
    (cell12701 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · norm_num [cell12701]
  · have h := gap_lower (n := 12701) (a := (667325483559 / 800000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251422792747 / 100000000000000 : ℝ))
      (E := (cell12701 ⟨19, by decide⟩).energy) (xi := (334051457338871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12701 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12701]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12701])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12701) (a := (667325483559 / 800000000000 : ℝ)) (b := (81088213381 / 50000000000000 : ℝ)) (q := (2251422792747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12701])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12701]

theorem cert12702_0 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (8407596016241 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450244818921 / 20000000000000 : ℝ))
      (E := (cell12702 ⟨0, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (8407596016241 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450244818921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_1 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (42020492902029 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251228117991 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨1, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (42020492902029 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251228117991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_2 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (21001509094769 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251232110693 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨2, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (21001509094769 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251232110693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_3 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16794222370193 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281404517429 / 12500000000000 : ℝ))
      (E := (cell12702 ⟨3, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16794222370193 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281404517429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_4 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83936212183417 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251240097053 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨4, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83936212183417 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251240097053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_5 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (16780267468063 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125622053833 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨5, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (16780267468063 / 20000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125622053833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_6 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (41933243642867 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125624060729 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨6, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (41933243642867 / 50000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125624060729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_7 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (1309869718499 / 1562500000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562813022067 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨7, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (1309869718499 / 1562500000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562813022067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_8 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83796861399369 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251256131583 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨8, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83796861399369 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251256131583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_9 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (8376208549667 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251260142737 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨9, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (8376208549667 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251260142737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_10 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83727334240659 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450252825743 / 20000000000000 : ℝ))
      (E := (cell12702 ⟨10, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83727334240659 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (450252825743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_11 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83692607596341 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562817024063 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨11, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83692607596341 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562817024063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_12 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83657905528901 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281409013741 / 12500000000000 : ℝ))
      (E := (cell12702 ⟨12, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83657905528901 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (281409013741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_13 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20905807000927 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125638058967 / 50000000000000 : ℝ))
      (E := (cell12702 ⟨13, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20905807000927 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (1125638058967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_14 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83588574986311 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251280126261 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨14, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83588574986311 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251280126261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_15 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83553946442437 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251284140653 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨15, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83553946442437 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251284140653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_16 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (8351934233799 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562822027107 / 25000000000000 : ℝ))
      (E := (cell12702 ⟨16, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (8351934233799 / 10000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (562822027107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_17 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83484762639053 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251292092979 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨17, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83484762639053 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251292092979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_18 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (20862551827971 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251296099319 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨18, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (20862551827971 / 25000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251296099319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12702_19 : CellCertificate 12702 (443317341233529 / 5000000000000000 : ℝ) (330726304770659 / 200000000000000000 : ℝ) (2672196134237 / 80000000000000 : ℝ)
    (cell12702 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · norm_num [cell12702]
  · have h := gap_lower (n := 12702) (a := (83415676322913 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251300132223 / 100000000000000 : ℝ))
      (E := (cell12702 ⟨19, by decide⟩).energy) (xi := (2672196134237 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12702 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12702]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12702])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12702) (a := (83415676322913 / 100000000000000 : ℝ)) (b := (20270437909 / 12500000000000 : ℝ)) (q := (2251300132223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12702])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12702]

theorem cert12703_0 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (84075945039103 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125550742403 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨0, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (84075945039103 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125550742403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_1 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (84040971000721 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140694092143 / 6250000000000 : ℝ))
      (E := (cell12703 ⟨1, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (84040971000721 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (140694092143 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_2 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (42003010947629 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562777372917 / 25000000000000 : ℝ))
      (E := (cell12703 ⟨2, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (42003010947629 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562777372917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_3 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83971097686213 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112555674399 / 5000000000000 : ℝ))
      (E := (cell12703 ⟨3, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83971097686213 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112555674399 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_4 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83936198337281 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125558735901 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨4, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83936198337281 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125558735901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_5 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41950661906173 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112556072573 / 5000000000000 : ℝ))
      (E := (cell12703 ⟨5, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41950661906173 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (112556072573 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_6 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83866474075483 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251125492971 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨6, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83866474075483 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251125492971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_7 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (16766329818191 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225112948827 / 10000000000000 : ℝ))
      (E := (cell12703 ⟨7, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (16766329818191 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225112948827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_8 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (20949212205803 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562783375711 / 25000000000000 : ℝ))
      (E := (cell12703 ⟨8, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (20949212205803 / 25000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562783375711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_9 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83762073236891 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125568742989 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨9, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83762073236891 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125568742989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_10 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83727322296813 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251141502701 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨10, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83727322296813 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251141502701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_11 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (5230787247999 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251145501749 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨11, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (5230787247999 / 6250000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251145501749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_12 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83657894215591 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (281393686201 / 12500000000000 : ℝ))
      (E := (cell12703 ⟨12, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83657894215591 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (281393686201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_13 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83623217005003 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125576736257 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨13, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83623217005003 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125576736257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_14 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (8358856430177 / 10000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251157456457 / 100000000000000 : ℝ))
      (E := (cell12703 ⟨14, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (8358856430177 / 10000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (2251157456457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_15 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83553936071619 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (35174398521 / 1562500000000 : ℝ))
      (E := (cell12703 ⟨15, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83553936071619 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (35174398521 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_16 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (10439916535057 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125582754187 / 50000000000000 : ℝ))
      (E := (cell12703 ⟨16, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (10439916535057 / 12500000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (1125582754187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_17 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (41742376447183 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225116947073 / 10000000000000 : ℝ))
      (E := (cell12703 ⟨17, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (41742376447183 / 50000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225116947073 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_18 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (16690039575921 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225117345559 / 10000000000000 : ℝ))
      (E := (cell12703 ⟨18, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (16690039575921 / 20000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (225117345559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12703_19 : CellCertificate 12703 (886606756288661 / 10000000000000000 : ℝ) (330700260921259 / 200000000000000000 : ℝ) (33399758062543 / 1000000000000000 : ℝ)
    (cell12703 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · norm_num [cell12703]
  · have h := gap_lower (n := 12703) (a := (83415667202607 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562794366931 / 25000000000000 : ℝ))
      (E := (cell12703 ⟨19, by decide⟩).energy) (xi := (33399758062543 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12703 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12703]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12703])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12703) (a := (83415667202607 / 100000000000000 : ℝ)) (b := (5067205683 / 3125000000000 : ℝ)) (q := (562794366931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12703])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12703]

theorem cert12704_0 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (84075929918179 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140686179393 / 6250000000000 : ℝ))
      (E := (cell12704 ⟨0, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (84075929918179 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (140686179393 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_1 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (8404095619973 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250982883737 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨1, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (8404095619973 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250982883737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_2 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (42003003706873 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250986868003 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨2, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (42003003706873 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250986868003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_3 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83971083523729 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250990889807 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨3, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83971083523729 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2250990889807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_4 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (671489475947 / 800000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562748710497 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨4, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (671489475947 / 800000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562748710497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_5 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10487663785821 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125499424329 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨5, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10487663785821 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125499424329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_6 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (10483307608423 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251002860001 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨6, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (10483307608423 / 12500000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251002860001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_7 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83831636200087 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225100688383 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨7, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83831636200087 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225100688383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_8 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (8379683624913 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125505434851 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨8, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (8379683624913 / 10000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125505434851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_9 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (20940515244787 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251014882877 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨9, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (20940515244787 / 25000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251014882877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_10 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (16745462070993 / 20000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251018872363 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨10, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (16745462070993 / 20000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251018872363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_11 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83692584341587 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562755711223 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨11, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83692584341587 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562755711223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_12 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41828941452101 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125513432521 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨12, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41828941452101 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125513432521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_13 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (4181160300409 / 5000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251030881003 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨13, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (4181160300409 / 5000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251030881003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_14 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (653035575149 / 781250000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562758724691 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨14, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (653035575149 / 781250000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562758724691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_15 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83553925702607 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125519432953 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨15, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83553925702607 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125519432953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_16 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (83519322224691 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562760711511 / 25000000000000 : ℝ))
      (E := (cell12704 ⟨16, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (83519322224691 / 100000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (562760711511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_17 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (5217796446963 / 6250000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251046902641 / 100000000000000 : ℝ))
      (E := (cell12704 ⟨17, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (5217796446963 / 6250000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (2251046902641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_18 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41725094224509 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125525433041 / 50000000000000 : ℝ))
      (E := (cell12704 ⟨18, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41725094224509 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (1125525433041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12704_19 : CellCertificate 12704 (886578834331461 / 10000000000000000 : ℝ) (826685552933271 / 500000000000000000 : ℝ) (41746331109389 / 1250000000000000 : ℝ)
    (cell12704 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · norm_num [cell12704]
  · have h := gap_lower (n := 12704) (a := (41707829041977 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225105485751 / 10000000000000 : ℝ))
      (E := (cell12704 ⟨19, by decide⟩).energy) (xi := (41746331109389 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12704 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12704]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12704])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12704) (a := (41707829041977 / 50000000000000 : ℝ)) (b := (81068831257 / 50000000000000 : ℝ)) (q := (225105485751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12704])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12704]

theorem cert12705_0 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (2101897869991 / 2500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (112542815443 / 5000000000000 : ℝ))
      (E := (cell12705 ⟨0, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (2101897869991 / 2500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (112542815443 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_1 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (84040941401083 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250860288507 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨1, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (84040941401083 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250860288507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_2 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (4200299646727 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562716074389 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨2, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (4200299646727 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562716074389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_3 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (10496383670439 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125434143517 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨3, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (10496383670439 / 12500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125434143517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_4 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (5246010665731 / 6250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90034892937 / 4000000000000 : ℝ))
      (E := (cell12705 ⟨4, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (5246010665731 / 6250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (90034892937 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_5 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41950648381489 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125438149633 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨5, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41950648381489 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125438149633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_6 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (16773289532287 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250880280503 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨6, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (16773289532287 / 20000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250880280503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_7 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20957905827833 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562721068737 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨7, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20957905827833 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562721068737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_8 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83796823677121 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250888290157 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨8, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83796823677121 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250888290157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_9 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (1047025609043 / 1250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (450178455083 / 20000000000000 : ℝ))
      (E := (cell12705 ⟨9, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (1047025609043 / 1250000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (450178455083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_10 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (41863649207557 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250896295747 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨10, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (41863649207557 / 50000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250896295747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_11 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20923143179287 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250900299889 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨11, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20923143179287 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250900299889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_12 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83657871594733 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562726073581 / 25000000000000 : ℝ))
      (E := (cell12705 ⟨12, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83657871594733 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (562726073581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_13 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (2090579875331 / 2500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250908285287 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨13, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (2090579875331 / 2500000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250908285287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_14 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83588542938219 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125456139383 / 50000000000000 : ℝ))
      (E := (cell12705 ⟨14, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83588542938219 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (1125456139383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_15 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83553915335401 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (281364535063 / 12500000000000 : ℝ))
      (E := (cell12705 ⟨15, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83553915335401 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (281364535063 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_16 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83519312170693 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250920295999 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨16, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83519312170693 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250920295999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_17 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (4174236670509 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (281365541313 / 12500000000000 : ℝ))
      (E := (cell12705 ⟨17, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (4174236670509 / 5000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (281365541313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_18 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (83450179020123 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250928330797 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨18, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (83450179020123 / 100000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250928330797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12705_19 : CellCertificate 12705 (443275458297227 / 5000000000000000 : ℝ) (1653240927629193 / 1000000000000000000 : ℝ) (333943721527497 / 10000000000000000 : ℝ)
    (cell12705 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · norm_num [cell12705]
  · have h := gap_lower (n := 12705) (a := (20853912241739 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250932301579 / 100000000000000 : ℝ))
      (E := (cell12705 ⟨19, by decide⟩).energy) (xi := (333943721527497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12705 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12705]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12705])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12705) (a := (20853912241739 / 25000000000000 : ℝ)) (b := (32424949049 / 20000000000000 : ℝ)) (q := (2250932301579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12705])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12705]

theorem cert12706_0 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (84075899683483 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450146748543 / 20000000000000 : ℝ))
      (E := (cell12706 ⟨0, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (84075899683483 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450146748543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_1 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (4202046330239 / 5000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125368873217 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨1, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (4202046330239 / 5000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125368873217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_2 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (42002989228819 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250741780329 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨2, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (42002989228819 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250741780329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_3 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83971055205561 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281343217193 / 12500000000000 : ℝ))
      (E := (cell12706 ⟨3, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83971055205561 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281343217193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_4 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16787231362449 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125374871199 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨4, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16787231362449 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125374871199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_5 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41950641620789 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125376872677 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨5, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41950641620789 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125376872677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_6 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83866434457637 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562689438619 / 25000000000000 : ℝ))
      (E := (cell12706 ⟨6, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83866434457637 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562689438619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_7 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (5239475651543 / 6250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281345222197 / 12500000000000 : ℝ))
      (E := (cell12706 ⟨7, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (5239475651543 / 6250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (281345222197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_8 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (16759362221437 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225076576421 / 10000000000000 : ℝ))
      (E := (cell12706 ⟨8, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (16759362221437 / 20000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (225076576421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_9 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83762036469767 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125384889817 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨9, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83762036469767 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125384889817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_10 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83727286477259 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125386886427 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨10, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83727286477259 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125386886427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_11 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83692561094667 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562694437651 / 25000000000000 : ℝ))
      (E := (cell12706 ⟨11, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83692561094667 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (562694437651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_12 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (5228616267949 / 6250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450156355491 / 20000000000000 : ℝ))
      (E := (cell12706 ⟨12, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (5228616267949 / 6250000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (450156355491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_13 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83623184020181 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125392871741 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨13, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83623184020181 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125392871741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_14 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83588532259209 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250789770881 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨14, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83588532259209 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250789770881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_15 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (8355390497 / 10000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250793749139 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨15, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (8355390497 / 10000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250793749139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_16 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41759651059231 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250797741867 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨16, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41759651059231 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250797741867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_17 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (41742361835341 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125400877159 / 50000000000000 : ℝ))
      (E := (cell12706 ⟨17, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (41742361835341 / 50000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (1125400877159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_18 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83450169592919 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250805791503 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨18, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83450169592919 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250805791503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12706_19 : CellCertificate 12706 (443261501538319 / 5000000000000000 : ℝ) (330622153977881 / 200000000000000000 : ℝ) (333916798581413 / 10000000000000000 : ℝ)
    (cell12706 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · norm_num [cell12706]
  · have h := gap_lower (n := 12706) (a := (83415639851611 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250809741679 / 100000000000000 : ℝ))
      (E := (cell12706 ⟨19, by decide⟩).energy) (xi := (333916798581413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12706 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12706]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12706])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12706) (a := (83415639851611 / 100000000000000 : ℝ)) (b := (162111830049 / 100000000000000 : ℝ)) (q := (2250809741679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12706])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12706]

theorem cert12707_0 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (21018971142427 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (70331600927 / 3125000000000 : ℝ))
      (E := (cell12707 ⟨0, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (21018971142427 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (70331600927 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_1 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (84040911810821 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125307628759 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨1, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (84040911810821 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125307628759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_2 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (42002981991521 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (70331851827 / 3125000000000 : ℝ))
      (E := (cell12707 ⟨2, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (42002981991521 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (70331851827 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_3 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20992760262469 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125311620669 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨3, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20992760262469 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125311620669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_4 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83936142975021 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250627272623 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨4, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83936142975021 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250627272623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_5 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41950634861183 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562657811213 / 25000000000000 : ℝ))
      (E := (cell12707 ⟨5, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41950634861183 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562657811213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_6 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20966605313997 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562658820481 / 25000000000000 : ℝ))
      (E := (cell12707 ⟨6, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20966605313997 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (562658820481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_7 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16766319508031 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125319637883 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨7, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16766319508031 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125319637883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_8 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41898399269661 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281330404233 / 12500000000000 : ℝ))
      (E := (cell12707 ⟨8, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41898399269661 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281330404233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_9 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (5235126513633 / 6250000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125323639747 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨9, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (5235126513633 / 6250000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125323639747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_10 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83727274541399 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125325622821 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨10, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83727274541399 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125325622821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_11 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (2615392171067 / 3125000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125327627553 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨11, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (2615392171067 / 3125000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125327627553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_12 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (16731569796311 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250659256343 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨12, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (16731569796311 / 20000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250659256343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_13 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83623173029003 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250663255591 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨13, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83623173029003 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250663255591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_14 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (41794260791021 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250667258833 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨14, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (41794260791021 / 50000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250667258833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_15 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (20888473651601 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250671271811 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨15, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (20888473651601 / 25000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250671271811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_16 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83519292067999 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125337620917 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨16, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83519292067999 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125337620917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_17 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (5217794620807 / 6250000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281334911313 / 12500000000000 : ℝ))
      (E := (cell12707 ⟨17, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (5217794620807 / 6250000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (281334911313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_18 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83450160167407 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250683248201 / 100000000000000 : ℝ))
      (E := (cell12707 ⟨18, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83450160167407 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (2250683248201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12707_19 : CellCertificate 12707 (88649509377701 / 1000000000000000 : ℝ) (1652980632642337 / 1000000000000000000 : ℝ) (41736235004461 / 1250000000000000 : ℝ)
    (cell12707 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · norm_num [cell12707]
  · have h := gap_lower (n := 12707) (a := (83415630737919 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125343647161 / 50000000000000 : ℝ))
      (E := (cell12707 ⟨19, by decide⟩).energy) (xi := (41736235004461 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12707 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12707]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12707])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12707) (a := (83415630737919 / 100000000000000 : ℝ)) (b := (6483956677 / 4000000000000 : ℝ)) (q := (1125343647161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12707])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12707]

theorem cert12708_0 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16815173891663 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (225048876971 / 10000000000000 : ℝ))
      (E := (cell12708 ⟨0, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16815173891663 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (225048876971 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_1 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (21010224254801 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (281311595491 / 12500000000000 : ℝ))
      (E := (cell12708 ⟨1, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (21010224254801 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (281311595491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_2 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (84005949510749 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250496789823 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨2, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (84005949510749 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250496789823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_3 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (10496378362057 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250500798419 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨3, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (10496378362057 / 12500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250500798419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_4 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83936129140023 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125252399147 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨4, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83936129140023 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125252399147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_5 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83901256205341 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562627199441 / 25000000000000 : ℝ))
      (E := (cell12708 ⟨5, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83901256205341 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562627199441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_6 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83866408056489 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125256402447 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨6, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83866408056489 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125256402447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_7 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41915792328867 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250516769519 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨7, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41915792328867 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250516769519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_8 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83796785973531 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250520815117 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨8, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83796785973531 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250520815117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_9 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83762011968523 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562631193749 / 25000000000000 : ℝ))
      (E := (cell12708 ⟨9, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83762011968523 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (562631193749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_10 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (5232953912971 / 6250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450105754431 / 20000000000000 : ℝ))
      (E := (cell12708 ⟨10, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (5232953912971 / 6250000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450105754431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_11 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41846268927789 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250532813397 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨11, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41846268927789 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250532813397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_12 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (20914459419461 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450107357817 / 20000000000000 : ℝ))
      (E := (cell12708 ⟨12, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (20914459419461 / 25000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450107357817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_13 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41811581019853 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125270381749 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨13, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41811581019853 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125270381749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_14 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (41794255453359 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250544800761 / 100000000000000 : ℝ))
      (E := (cell12708 ⟨14, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (41794255453359 / 50000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (2250544800761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_15 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83553884244613 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (56263719759 / 2500000000000 : ℝ))
      (E := (cell12708 ⟨15, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83553884244613 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (56263719759 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_16 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83519282019301 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (8791221859 / 390625000000 : ℝ))
      (E := (cell12708 ⟨16, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83519282019301 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (8791221859 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_17 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (83484704196871 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450111364529 / 20000000000000 : ℝ))
      (E := (cell12708 ⟨17, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (83484704196871 / 100000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (450111364529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_18 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (16690030148717 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125280408679 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨18, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (16690030148717 / 20000000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125280408679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12708_19 : CellCertificate 12708 (886467188694569 / 10000000000000000 : ℝ) (1652850515883151 / 1000000000000000000 : ℝ) (6677259317783 / 200000000000000 : ℝ)
    (cell12708 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · norm_num [cell12708]
  · have h := gap_lower (n := 12708) (a := (2085390540647 / 2500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125282392371 / 50000000000000 : ℝ))
      (E := (cell12708 ⟨19, by decide⟩).energy) (xi := (6677259317783 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12708 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12708]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12708])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12708) (a := (2085390540647 / 2500000000000 : ℝ)) (b := (10130375367 / 6250000000000 : ℝ)) (q := (1125282392371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12708])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12708]

theorem cert12709_0 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (84075854349303 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562591590713 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨0, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (84075854349303 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562591590713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_1 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (8404088222993 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562592595333 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨1, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (8404088222993 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562592595333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_2 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (2100148376019 / 2500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562593593601 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨2, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (2100148376019 / 2500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562593593601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_3 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83971012745301 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (281297293863 / 12500000000000 : ℝ))
      (E := (cell12709 ⟨3, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83971012745301 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (281297293863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_4 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (20984028826813 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (70324449291 / 3125000000000 : ℝ))
      (E := (cell12709 ⟨4, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (20984028826813 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (70324449291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_5 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (10487655336313 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250386346159 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨5, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (10487655336313 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250386346159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_6 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41933197429569 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250390323389 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨6, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41933197429569 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250390323389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_7 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41915785888711 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450078874957 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨7, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41915785888711 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450078874957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_8 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (20949193352453 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (90015933359 / 4000000000000 : ℝ))
      (E := (cell12709 ⟨8, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (20949193352453 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (90015933359 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_9 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (10470249965119 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250402382183 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨9, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (10470249965119 / 12500000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250402382183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_10 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83727250675667 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562601588099 / 25000000000000 : ℝ))
      (E := (cell12709 ⟨10, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83727250675667 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (562601588099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_11 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83692526238969 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (140650647963 / 6250000000000 : ℝ))
      (E := (cell12709 ⟨11, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83692526238969 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (140650647963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_12 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (20914456594013 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250414375677 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨12, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (20914456594013 / 25000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250414375677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_13 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83623151052289 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450083676687 / 20000000000000 : ℝ))
      (E := (cell12709 ⟨13, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83623151052289 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (450083676687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_14 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (16717700046647 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (70325698079 / 3125000000000 : ℝ))
      (E := (cell12709 ⟨14, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (16717700046647 / 20000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (70325698079 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_15 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (668430991077 / 800000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250426362949 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨15, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (668430991077 / 800000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250426362949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_16 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (8351927197237 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225043034589 / 10000000000000 : ℝ))
      (E := (cell12709 ⟨16, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (8351927197237 / 10000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (225043034589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_17 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (41742347231279 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250434350741 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨17, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (41742347231279 / 50000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250434350741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_18 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83450141321453 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250438382509 / 100000000000000 : ℝ))
      (E := (cell12709 ⟨18, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83450141321453 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (2250438382509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12709_19 : CellCertificate 12709 (110804910978539 / 1250000000000000 : ℝ) (1652720419607007 / 1000000000000000000 : ℝ) (83459014035157 / 2500000000000000 : ℝ)
    (cell12709 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · norm_num [cell12709]
  · have h := gap_lower (n := 12709) (a := (83415612515493 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125221193853 / 50000000000000 : ℝ))
      (E := (cell12709 ⟨19, by decide⟩).energy) (xi := (83459014035157 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12709 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12709]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12709])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12709) (a := (83415612515493 / 100000000000000 : ℝ)) (b := (162073096891 / 100000000000000 : ℝ)) (q := (1125221193853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12709])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12709]

theorem cert12710_0 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (5254739952667 / 6250000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125121975641 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨0, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (5254739952667 / 6250000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125121975641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_1 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (84040867442997 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250247936229 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨1, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (84040867442997 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250247936229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_2 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (84005920573073 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125125977177 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨2, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (84005920573073 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125125977177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_3 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83970998596409 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250255956679 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨3, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83970998596409 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250255956679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_4 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41968050738353 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250259951777 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨4, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41968050738353 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250259951777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_5 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41950614588927 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250263947969 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨5, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41950614588927 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250263947969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_6 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16773276332787 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250267953313 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨6, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16773276332787 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250267953313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_7 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (4191577944961 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (35160499619 / 1562500000000 : ℝ))
      (E := (cell12710 ⟨7, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (4191577944961 / 5000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (35160499619 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_8 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20949190212041 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125137982217 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨8, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20949190212041 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125137982217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_9 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83761987475413 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250279926993 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨9, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83761987475413 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250279926993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_10 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83727238745793 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1758034319 / 78125000000 : ℝ))
      (E := (cell12710 ⟨10, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83727238745793 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1758034319 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_11 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (20923128656079 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562571993803 / 25000000000000 : ℝ))
      (E := (cell12710 ⟨11, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (20923128656079 / 25000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (562571993803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_12 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83657815076177 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (140643247377 / 6250000000000 : ℝ))
      (E := (cell12710 ⟨12, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83657815076177 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (140643247377 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_13 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83623140066751 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250295941059 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨13, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83623140066751 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250295941059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_14 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16717697912319 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125149965137 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨14, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16717697912319 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125149965137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_15 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41776931763221 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (281287991427 / 12500000000000 : ℝ))
      (E := (cell12710 ⟨15, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41776931763221 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (281287991427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_16 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (16703852385441 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250307949979 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨16, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (16703852385441 / 20000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250307949979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_17 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83484684729973 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250311933003 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨17, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83484684729973 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250311933003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_18 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (83450131901011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250315943657 / 100000000000000 : ℝ))
      (E := (cell12710 ⟨18, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (83450131901011 / 100000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (2250315943657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12710_19 : CellCertificate 12710 (443205695588619 / 5000000000000000 : ℝ) (1652590343809071 / 1000000000000000000 : ℝ) (333809150788951 / 10000000000000000 : ℝ)
    (cell12710 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · norm_num [cell12710]
  · have h := gap_lower (n := 12710) (a := (41707801703379 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125159993353 / 50000000000000 : ℝ))
      (E := (cell12710 ⟨19, by decide⟩).energy) (xi := (333809150788951 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12710 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12710]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12710])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12710) (a := (41707801703379 / 50000000000000 : ℝ)) (b := (8103009499 / 5000000000000 : ℝ)) (q := (1125159993353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12710])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12710]

theorem cert12711_0 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (84075824138421 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250121592811 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨0, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (84075824138421 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250121592811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_1 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16808170531681 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562531400531 / 25000000000000 : ℝ))
      (E := (cell12711 ⟨1, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16808170531681 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562531400531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_2 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (84005906107689 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250129587529 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨2, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (84005906107689 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250129587529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_3 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41985492224891 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (112506677893 / 5000000000000 : ℝ))
      (E := (cell12711 ⟨3, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41985492224891 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (112506677893 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_4 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16787217529677 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450027515919 / 20000000000000 : ℝ))
      (E := (cell12711 ⟨4, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16787217529677 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (450027515919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_5 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (8390121566739 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125070801597 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨5, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (8390121566739 / 10000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125070801597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_6 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (524164802943 / 625000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562536394691 / 25000000000000 : ℝ))
      (E := (cell12711 ⟨6, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (524164802943 / 625000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (562536394691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_7 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83831546023127 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125074786007 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨7, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83831546023127 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125074786007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_8 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83796748288587 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250153590499 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨8, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83796748288587 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250153590499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_9 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41880987615953 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250157583493 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨9, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41880987615953 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250157583493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_10 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (10465903352239 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125080778987 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨10, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (10465903352239 / 12500000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125080778987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_11 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83692503011619 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125082789369 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨11, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83692503011619 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125082789369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_12 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (4182890188911 / 5000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125084797121 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨12, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (4182890188911 / 5000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125084797121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_13 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41811564541547 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125086805357 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨13, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41811564541547 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125086805357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_14 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16717695778359 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281272197 / 12500000000 : ℝ))
      (E := (cell12711 ⟨14, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16717695778359 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281272197 / 12500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_15 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (83553853170061 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250181612089 / 100000000000000 : ℝ))
      (E := (cell12711 ⟨15, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (83553853170061 / 100000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (2250181612089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_16 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (20879812970951 / 25000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125092804087 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨16, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (20879812970951 / 25000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125092804087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_17 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (16696934999823 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281273696179 / 12500000000000 : ℝ))
      (E := (cell12711 ⟨17, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (16696934999823 / 20000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (281273696179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_18 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (41725061241129 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125096808633 / 50000000000000 : ℝ))
      (E := (cell12711 ⟨18, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (41725061241129 / 50000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (1125096808633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12711_19 : CellCertificate 12711 (177276699748069 / 2000000000000000 : ℝ) (1652460288484507 / 1000000000000000000 : ℝ) (6675644996659 / 200000000000000 : ℝ)
    (cell12711 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · norm_num [cell12711]
  · have h := gap_lower (n := 12711) (a := (3336623771987 / 4000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (112509879087 / 5000000000000 : ℝ))
      (E := (cell12711 ⟨19, by decide⟩).energy) (xi := (6675644996659 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12711 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12711]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12711])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12711) (a := (3336623771987 / 4000000000000 : ℝ)) (b := (162047285139 / 100000000000000 : ℝ)) (q := (112509879087 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12711])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12711]

theorem cert12712_0 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (84075809036549 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2249999229631 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨0, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (84075809036549 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2249999229631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_1 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (42020418938077 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562500815837 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨1, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (42020418938077 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562500815837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_2 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (84005891644607 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250007273931 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨2, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (84005891644607 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250007273931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_3 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83970970305417 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125005635107 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨3, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83970970305417 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125005635107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_4 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (5246004613893 / 6250000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250015260767 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨4, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (5246004613893 / 6250000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250015260767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_5 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (10487650269889 / 12500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250019253907 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨5, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (10487650269889 / 12500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250019253907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_6 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83866355279973 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250023257693 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨6, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83866355279973 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250023257693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_7 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83831533149143 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250027279929 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨7, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83831533149143 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250027279929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_8 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (2094918393277 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250031270169 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨8, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (2094918393277 / 2500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250031270169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_9 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83761962990431 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125017617819 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨9, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83761962990431 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125017617819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_10 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (3349088595681 / 4000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250039241359 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨10, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (3349088595681 / 4000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250039241359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_11 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (20923122850219 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250043236059 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨11, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (20923122850219 / 25000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250043236059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_12 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (4182889624109 / 5000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (281255903277 / 12500000000000 : ℝ))
      (E := (cell12712 ⟨12, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (4182889624109 / 5000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (281255903277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_13 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41811559050657 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125025638087 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨13, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41811559050657 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125025638087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_14 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83588468223837 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125027637853 / 50000000000000 : ℝ))
      (E := (cell12712 ⟨14, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83588468223837 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (1125027637853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_15 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83553842815483 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (28125740381 / 1250000000000 : ℝ))
      (E := (cell12712 ⟨15, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83553842815483 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (28125740381 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_16 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (10439905230271 / 12500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250063262289 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨16, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (10439905230271 / 12500000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250063262289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_17 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (83484665269983 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (225006726003 / 10000000000000 : ℝ))
      (E := (cell12712 ⟨17, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (83484665269983 / 100000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (225006726003 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_18 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41725056532597 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250071286873 / 100000000000000 : ℝ))
      (E := (cell12712 ⟨18, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41725056532597 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (2250071286873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12712_19 : CellCertificate 12712 (443177805258317 / 5000000000000000 : ℝ) (1652330253628481 / 1000000000000000000 : ℝ) (10429854789733 / 312500000000000 : ℝ)
    (cell12712 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · norm_num [cell12712]
  · have h := gap_lower (n := 12712) (a := (41707792597121 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562518822331 / 25000000000000 : ℝ))
      (E := (cell12712 ⟨19, by decide⟩).energy) (xi := (10429854789733 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12712 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12712]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12712])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12712) (a := (41707792597121 / 50000000000000 : ℝ)) (b := (5063574449 / 3125000000000 : ℝ)) (q := (562518822331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12712])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12712]

theorem cert12713_0 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (2627368560533 / 3125000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562469244341 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨0, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (2627368560533 / 3125000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562469244341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_1 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (84040823096243 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249880977737 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨1, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (84040823096243 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249880977737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_2 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (42002938591913 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281235619463 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨2, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (42002938591913 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281235619463 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_3 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16794191232663 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124944488989 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨3, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16794191232663 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124944488989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_4 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (16787211999683 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562473234347 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨4, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (16787211999683 / 20000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562473234347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_5 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83901188653019 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124948479019 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨5, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83901188653019 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124948479019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_6 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20966585522803 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281237616519 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨6, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20966585522803 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281237616519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_7 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83831520277267 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124952462719 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨7, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83831520277267 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124952462719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_8 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83796723175643 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249908945447 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨8, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83796723175643 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249908945447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_9 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20940487687747 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249912941451 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨9, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20940487687747 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249912941451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_10 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (20931800742033 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124958489237 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨10, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (20931800742033 / 25000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124958489237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_11 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83692479792089 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249920947173 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨11, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83692479792089 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249920947173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_12 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83657781188057 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124962485069 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨12, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83657781188057 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124962485069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_13 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41811553560707 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562482234359 / 25000000000000 : ℝ))
      (E := (cell12713 ⟨13, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41811553560707 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (562482234359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_14 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41794228778859 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281241621407 / 12500000000000 : ℝ))
      (E := (cell12713 ⟨14, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41794228778859 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (281241621407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_15 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83553832462707 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249936961079 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨15, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83553832462707 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249936961079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_16 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83519231802297 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (224994097051 / 10000000000000 : ℝ))
      (E := (cell12713 ⟨16, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83519231802297 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (224994097051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_17 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (41742327771289 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249944946587 / 100000000000000 : ℝ))
      (E := (cell12713 ⟨17, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (41742327771289 / 50000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (2249944946587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_18 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83450103649819 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124974476239 / 50000000000000 : ℝ))
      (E := (cell12713 ⟨18, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83450103649819 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (1124974476239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12713_19 : CellCertificate 12713 (443163863252551 / 5000000000000000 : ℝ) (1652200239236163 / 1000000000000000000 : ℝ) (166864230551649 / 5000000000000000 : ℝ)
    (cell12713 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · norm_num [cell12713]
  · have h := gap_lower (n := 12713) (a := (83415576090461 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (449990598589 / 20000000000000 : ℝ))
      (E := (cell12713 ⟨19, by decide⟩).energy) (xi := (166864230551649 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12713 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12713]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12713])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12713) (a := (83415576090461 / 100000000000000 : ℝ)) (b := (81010740833 / 50000000000000 : ℝ)) (q := (449990598589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12713])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12713]

theorem cert12714_0 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (42037889419971 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249754662577 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨0, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (42037889419971 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249754662577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_1 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (5252550519917 / 6250000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249758687459 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨1, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (5252550519917 / 6250000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249758687459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_2 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (42002931362673 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562440672677 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨2, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (42002931362673 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562440672677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_3 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (3358837680939 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124883340577 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨3, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (3358837680939 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124883340577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_4 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (16787209235353 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249770667367 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨4, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (16787209235353 / 20000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249770667367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_5 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83901175149111 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (112488732883 / 5000000000000 : ℝ))
      (E := (cell12714 ⟨5, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83901175149111 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (112488732883 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_6 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83866328904597 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124889330047 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨6, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83866328904597 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124889330047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_7 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (41915753703749 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562445670617 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨7, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (41915753703749 / 50000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562445670617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_8 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (3351868424891 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249786674333 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨8, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (3351868424891 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249786674333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_9 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (3350477540543 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249790700937 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨9, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (3350477540543 / 4000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249790700937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_10 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (8372719104623 / 10000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (28122433891 / 1250000000000 : ℝ))
      (E := (cell12714 ⟨10, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (8372719104623 / 10000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (28122433891 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_11 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (10461558523157 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449959742417 / 20000000000000 : ℝ))
      (E := (cell12714 ⟨11, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (10461558523157 / 12500000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449959742417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_12 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83657769895849 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249802709829 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨12, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83657769895849 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249802709829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_13 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83623096143391 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249806710737 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨13, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83623096143391 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249806710737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_14 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83588446893439 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249810720791 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨14, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83588446893439 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249810720791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_15 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83553822111733 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124907343781 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨15, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83553822111733 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124907343781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_16 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83519221764189 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124909337327 / 50000000000000 : ℝ))
      (E := (cell12714 ⟨16, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83519221764189 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (1124909337327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_17 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83484645816899 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562455671829 / 25000000000000 : ℝ))
      (E := (cell12714 ⟨17, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83484645816899 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (562455671829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_18 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83450094236131 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249826672317 / 100000000000000 : ℝ))
      (E := (cell12714 ⟨18, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83450094236131 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (2249826672317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12714_19 : CellCertificate 12714 (886299846704751 / 10000000000000000 : ℝ) (826035122651361 / 500000000000000000 : ℝ) (333701573327309 / 10000000000000000 : ℝ)
    (cell12714 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · norm_num [cell12714]
  · have h := gap_lower (n := 12714) (a := (83415566988329 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449966138521 / 20000000000000 : ℝ))
      (E := (cell12714 ⟨19, by decide⟩).energy) (xi := (333701573327309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12714 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12714]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12714])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12714) (a := (83415566988329 / 100000000000000 : ℝ)) (b := (20251072879 / 12500000000000 : ℝ)) (q := (449966138521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12714])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12714]

theorem cert12715_0 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (16815152749041 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562408114677 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨0, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (16815152749041 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562408114677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_1 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (84040793543439 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249636450349 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨1, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (84040793543439 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249636450349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_2 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (42002924134583 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124820239471 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨2, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (42002924134583 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124820239471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_3 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83970927885897 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249644437623 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨3, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83970927885897 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249644437623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_4 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41968016178669 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124824225351 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨4, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41968016178669 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124824225351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_5 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41950580823693 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249652468633 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨5, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41950580823693 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249652468633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_6 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (1310411183127 / 1562500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124828220759 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨6, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (1310411183127 / 1562500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124828220759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_7 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83831494539837 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562415108767 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨7, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83831494539837 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562415108767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_8 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (1309323407359 / 1562500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562416114207 / 25000000000000 : ℝ))
      (E := (cell12715 ⟨8, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (1309323407359 / 1562500000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (562416114207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_9 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83761926278193 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281208557009 / 12500000000000 : ℝ))
      (E := (cell12715 ⟨9, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83761926278193 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (281208557009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_10 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83727179126321 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249672439773 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨10, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83727179126321 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249672439773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_11 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (10461557072547 / 12500000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (89987058909 / 4000000000000 : ℝ))
      (E := (cell12715 ⟨11, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (10461557072547 / 12500000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (89987058909 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_12 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41828879302779 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449936089057 / 20000000000000 : ℝ))
      (E := (cell12715 ⟨12, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41828879302779 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (449936089057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_13 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (41811542583623 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249684479843 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨13, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (41811542583623 / 50000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249684479843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_14 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83588436231 / 100000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224968846617 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨14, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83588436231 / 100000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224968846617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_15 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83553811762561 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224969246809 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨15, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83553811762561 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224969246809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_16 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (16703842345569 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124848245547 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨16, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (16703842345569 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124848245547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_17 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (16696927218589 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249700482217 / 100000000000000 : ℝ))
      (E := (cell12715 ⟨17, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (16696927218589 / 20000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (2249700482217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_18 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83450084824131 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224970444639 / 10000000000000 : ℝ))
      (E := (cell12715 ⟨18, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83450084824131 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (224970444639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12715_19 : CellCertificate 12715 (44313598555729 / 500000000000000 : ℝ) (1651940271823329 / 1000000000000000000 : ℝ) (333674689942321 / 10000000000000000 : ℝ)
    (cell12715 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · norm_num [cell12715]
  · have h := gap_lower (n := 12715) (a := (83415557887847 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124854223281 / 50000000000000 : ℝ))
      (E := (cell12715 ⟨19, by decide⟩).energy) (xi := (333674689942321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12715 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12715]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12715])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12715) (a := (83415557887847 / 100000000000000 : ℝ)) (b := (80997843233 / 50000000000000 : ℝ)) (q := (1124854223281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12715])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12715]

theorem cert12716_0 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16815149730569 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562377562533 / 25000000000000 : ℝ))
      (E := (cell12716 ⟨0, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16815149730569 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562377562533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_1 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16808155754109 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281189283301 / 12500000000000 : ℝ))
      (E := (cell12716 ⟨1, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16808155754109 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281189283301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_2 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16801166763057 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249518262551 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨2, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16801166763057 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249518262551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_3 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83970913750579 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249522247389 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨3, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83970913750579 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249522247389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_4 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83936018540133 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249526229491 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨4, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83936018540133 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249526229491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_5 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41950574073923 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281191284387 / 12500000000000 : ℝ))
      (E := (cell12716 ⟨5, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41950574073923 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281191284387 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_6 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (20966575634451 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562383569107 / 25000000000000 : ℝ))
      (E := (cell12716 ⟨6, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (20966575634451 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (562383569107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_7 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (41915740837141 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (35149035019 / 1562500000000 : ℝ))
      (E := (cell12716 ⟨7, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (41915740837141 / 50000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (35149035019 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_8 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16759337104349 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124771117467 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨8, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16759337104349 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124771117467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_9 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83761914044841 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249546264879 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨9, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83761914044841 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249546264879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_10 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83727167208403 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140596892503 / 6250000000000 : ℝ))
      (E := (cell12716 ⟨10, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83727167208403 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (140596892503 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_11 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (1673848899549 / 2000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124777143581 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨11, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (1673848899549 / 2000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124777143581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_12 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83657747317181 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249558234603 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨12, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83657747317181 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249558234603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_13 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83623074192977 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124781122379 / 50000000000000 : ℝ))
      (E := (cell12716 ⟨13, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83623074192977 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (1124781122379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_14 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (104485531963 / 125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449913253107 / 20000000000000 : ℝ))
      (E := (cell12716 ⟨14, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (104485531963 / 125000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449913253107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_15 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83553801415189 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449914048901 / 20000000000000 : ℝ))
      (E := (cell12716 ⟨15, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83553801415189 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449914048901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_16 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83519201693263 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281196780659 / 12500000000000 : ℝ))
      (E := (cell12716 ⟨16, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83519201693263 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (281196780659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_17 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (20871156592679 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (56239456827 / 2500000000000 : ℝ))
      (E := (cell12716 ⟨17, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (20871156592679 / 25000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (56239456827 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_18 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (83450075413819 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249582274697 / 100000000000000 : ℝ))
      (E := (cell12716 ⟨18, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (83450075413819 / 100000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (2249582274697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12716_19 : CellCertificate 12716 (886244099733589 / 10000000000000000 : ℝ) (1651810318793157 / 1000000000000000000 : ℝ) (333647810947167 / 10000000000000000 : ℝ)
    (cell12716 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · norm_num [cell12716]
  · have h := gap_lower (n := 12716) (a := (16683109757803 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449917250963 / 20000000000000 : ℝ))
      (E := (cell12716 ⟨19, by decide⟩).energy) (xi := (333647810947167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12716 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12716]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12716])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12716) (a := (16683109757803 / 20000000000000 : ℝ)) (b := (5061962249 / 3125000000000 : ℝ)) (q := (449917250963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12716])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12716]

theorem cert12717_0 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (42037866781431 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449877618933 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨0, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (42037866781431 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449877618933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_1 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (84040763999989 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249392077803 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨1, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (84040763999989 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249392077803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_2 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10500727420463 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249396099393 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨2, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10500727420463 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249396099393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_3 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41985449808761 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249400110451 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨3, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41985449808761 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249400110451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_4 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (1678720094503 / 2000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449880823909 / 20000000000000 : ℝ))
      (E := (cell12717 ⟨4, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (1678720094503 / 2000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (449880823909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_5 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83901134650489 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124704038527 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨5, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83901134650489 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124704038527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_6 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10483286169703 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249412106871 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨6, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10483286169703 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249412106871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_7 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41915734405417 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249416100911 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨7, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41915734405417 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249416100911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_8 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41898336487291 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562355016663 / 25000000000000 : ℝ))
      (E := (cell12717 ⟨8, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41898336487291 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562355016663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_9 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41880950906759 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249424069339 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨9, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41880950906759 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249424069339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_10 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83727155292477 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124714058007 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨10, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83727155292477 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124714058007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_11 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83692433376477 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (224943209733 / 10000000000000 : ℝ))
      (E := (cell12717 ⟨11, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83692433376477 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (224943209733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_12 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83657736030719 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249436077783 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨12, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83657736030719 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249436077783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_13 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (16724612644117 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (140590007607 / 6250000000000 : ℝ))
      (E := (cell12717 ⟨13, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (16724612644117 / 20000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (140590007607 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_14 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41794207455819 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249444118887 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨14, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41794207455819 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249444118887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_15 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (41776895534809 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249448074969 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨15, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (41776895534809 / 50000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249448074969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_16 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (20879797915111 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562363027937 / 25000000000000 : ℝ))
      (E := (cell12717 ⟨16, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (20879797915111 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (562363027937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_17 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (20871154162553 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249456118117 / 100000000000000 : ℝ))
      (E := (cell12717 ⟨17, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (20871154162553 / 25000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (2249456118117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_18 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (83450066005193 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (35147814047 / 1562500000000 : ℝ))
      (E := (cell12717 ⟨18, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (83450066005193 / 100000000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (35147814047 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12717_19 : CellCertificate 12717 (44310811628039 / 500000000000000 : ℝ) (1651680386207381 / 1000000000000000000 : ℝ) (333620936340679 / 10000000000000000 : ℝ)
    (cell12717 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · norm_num [cell12717]
  · have h := gap_lower (n := 12717) (a := (10426942461479 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124732058683 / 50000000000000 : ℝ))
      (E := (cell12717 ⟨19, by decide⟩).energy) (xi := (333620936340679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12717 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12717]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12717])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12717) (a := (10426942461479 / 12500000000000 : ℝ)) (b := (161969899537 / 100000000000000 : ℝ)) (q := (1124732058683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12717])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12717]

theorem cert12718_0 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (16815143695051 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124632967247 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨0, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (16815143695051 / 20000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124632967247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_1 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (8404074923177 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (224926994237 / 10000000000000 : ℝ))
      (E := (cell12718 ⟨1, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (8404074923177 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (224926994237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_2 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (84005804914421 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249273931613 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨2, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (84005804914421 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249273931613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_3 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (20992721371681 / 25000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249277968931 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨3, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (20992721371681 / 25000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249277968931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_4 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83935990912389 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249281947149 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨4, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83935990912389 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249281947149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_5 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41950560577657 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124642966219 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨5, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41950560577657 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124642966219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_6 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83866276179589 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249289932849 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨6, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83866276179589 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249289932849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_7 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83831455949491 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124646978091 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨7, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83831455949491 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124646978091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_8 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41898330214743 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249297951983 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨8, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41898330214743 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249297951983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_9 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (2617559049507 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249301985497 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨9, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (2617559049507 / 3125000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249301985497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_10 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83727143378541 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281163243459 / 12500000000000 : ℝ))
      (E := (cell12718 ⟨10, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83727143378541 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281163243459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_11 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (5230776361091 / 6250000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249309961299 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨11, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (5230776361091 / 6250000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249309961299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_12 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83657724746171 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124656987413 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨12, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83657724746171 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124656987413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_13 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (8362305225007 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562329498619 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨13, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (8362305225007 / 10000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562329498619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_14 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (41794202127357 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281165246011 / 12500000000000 : ℝ))
      (E := (cell12718 ⟨14, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (41794202127357 / 50000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (281165246011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_15 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83553780725847 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562331489871 / 25000000000000 : ℝ))
      (E := (cell12718 ⟨15, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83553780725847 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (562331489871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_16 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83519181629387 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249329974151 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨16, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83519181629387 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249329974151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_17 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (10435575866429 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249333959121 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨17, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (10435575866429 / 12500000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249333959121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_18 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83450056598253 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249337977557 / 100000000000000 : ℝ))
      (E := (cell12718 ⟨18, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83450056598253 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (2249337977557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12718_19 : CellCertificate 12718 (886188369595153 / 10000000000000000 : ℝ) (206443809257647 / 125000000000000000 : ℝ) (333594066121691 / 10000000000000000 : ℝ)
    (cell12718 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · norm_num [cell12718]
  · have h := gap_lower (n := 12718) (a := (83415530596297 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124670987981 / 50000000000000 : ℝ))
      (E := (cell12718 ⟨19, by decide⟩).energy) (xi := (333594066121691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12718 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12718]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12718])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12718) (a := (83415530596297 / 100000000000000 : ℝ)) (b := (40489252293 / 25000000000000 : ℝ)) (q := (1124670987981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12718])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12718]

theorem cert12719_0 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (10509462923753 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124571942623 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨0, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (10509462923753 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124571942623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_1 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (84040734465887 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249147860111 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨1, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (84040734465887 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249147860111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_2 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (21001447616859 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140571992183 / 6250000000000 : ℝ))
      (E := (cell12719 ⟨2, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (21001447616859 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (140571992183 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_3 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41985435679093 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224915588071 / 10000000000000 : ℝ))
      (E := (cell12719 ⟨3, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41985435679093 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224915588071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_4 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (10491997137731 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124579943011 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨4, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (10491997137731 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124579943011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_5 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83901107662321 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249163841247 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨5, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83901107662321 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249163841247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_6 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83866263003697 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562291967567 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨6, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83866263003697 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562291967567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_7 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83831443090253 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449834373001 / 20000000000000 : ℝ))
      (E := (cell12719 ⟨7, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83831443090253 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (449834373001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_8 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (10474580985807 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249175890929 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨8, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (10474580985807 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249175890929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_9 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (41880938678479 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124589919643 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨9, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (41880938678479 / 50000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124589919643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_10 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (16745426293319 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562295972779 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨10, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (16745426293319 / 20000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562295972779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_11 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83692410180387 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224918787907 / 10000000000000 : ℝ))
      (E := (cell12719 ⟨11, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83692410180387 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224918787907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_12 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83657713463537 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124595933821 / 50000000000000 : ℝ))
      (E := (cell12719 ⟨12, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83657713463537 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (1124595933821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_13 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83623041281429 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249195863053 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨13, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83623041281429 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249195863053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_14 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (20897098399907 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249199871279 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨14, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (20897098399907 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249199871279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_15 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (668430163071 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249203898051 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨15, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (668430163071 / 800000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249203898051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_16 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (20879792900023 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562301972667 / 25000000000000 : ℝ))
      (E := (cell12719 ⟨16, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (20879792900023 / 25000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (562301972667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_17 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (10435574651797 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (22492118543 / 1000000000000 : ℝ))
      (E := (cell12719 ⟨17, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (10435574651797 / 12500000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (22492118543 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_18 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83450047193 / 100000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224921585211 / 10000000000000 : ℝ))
      (E := (cell12719 ⟨18, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83450047193 / 100000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (224921585211 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12719_19 : CellCertificate 12719 (886160510835711 / 10000000000000000 : ℝ) (1651420582349719 / 1000000000000000000 : ℝ) (166783600144519 / 5000000000000000 : ℝ)
    (cell12719 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · norm_num [cell12719]
  · have h := gap_lower (n := 12719) (a := (83415521502411 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249219888857 / 100000000000000 : ℝ))
      (E := (cell12719 ⟨19, by decide⟩).energy) (xi := (166783600144519 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12719 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12719]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12719])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12719) (a := (83415521502411 / 100000000000000 : ℝ)) (b := (161944120873 / 100000000000000 : ℝ)) (q := (2249219888857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12719])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12719]

theorem cert12720_0 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (2627365259599 / 3125000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (449804354697 / 20000000000000 : ℝ))
      (E := (cell12720 ⟨0, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (2627365259599 / 3125000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (449804354697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_1 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (84040719702341 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249025773191 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨1, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (84040719702341 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249025773191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_2 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (21001444005687 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124514906811 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨2, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (21001444005687 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124514906811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_3 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41985428615953 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562258446977 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨3, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41985428615953 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562258446977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_4 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83935963293527 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124518910177 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨4, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83935963293527 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124518910177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_5 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (8390109417151 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124520901741 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨5, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (8390109417151 / 10000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124520901741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_6 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (20966562457487 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89961832129 / 4000000000000 : ℝ))
      (E := (cell12720 ⟨6, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (20966562457487 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (89961832129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_7 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (523946438957 / 625000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112452491369 / 5000000000000 : ℝ))
      (E := (cell12720 ⟨7, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (523946438957 / 625000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112452491369 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_8 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83796635345493 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249053825491 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨8, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83796635345493 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249053825491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_9 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (2094046628293 / 2500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249057804777 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨9, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (2094046628293 / 2500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249057804777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_10 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41863559778319 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (140566364391 / 6250000000000 : ℝ))
      (E := (cell12720 ⟨10, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41863559778319 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (140566364391 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_11 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83692398585269 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (35141653009 / 1562500000000 : ℝ))
      (E := (cell12720 ⟨11, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83692398585269 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (35141653009 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_12 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (2614303193213 / 3125000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249069814323 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨12, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (2614303193213 / 3125000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249069814323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_13 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (10452878789333 / 12500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249073785557 / 100000000000000 : ℝ))
      (E := (cell12720 ⟨13, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (10452878789333 / 12500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (2249073785557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_14 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83588382946379 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112453891423 / 5000000000000 : ℝ))
      (E := (cell12720 ⟨14, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83588382946379 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (112453891423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_15 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83553760043703 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562270458127 / 25000000000000 : ℝ))
      (E := (cell12720 ⟨15, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83553760043703 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (562270458127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_16 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (41759580786279 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124542901557 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨16, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (41759580786279 / 50000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124542901557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_17 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (83484587499043 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124544901829 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨17, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (83484587499043 / 100000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124544901829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_18 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (10431254723679 / 12500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124546919569 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨18, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (10431254723679 / 12500000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124546919569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12720_19 : CellCertificate 12720 (886132656281453 / 10000000000000000 : ℝ) (165129071106819 / 100000000000000000 : ℝ) (166770169420777 / 5000000000000000 : ℝ)
    (cell12720 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · norm_num [cell12720]
  · have h := gap_lower (n := 12720) (a := (20853878102543 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124548898899 / 50000000000000 : ℝ))
      (E := (cell12720 ⟨19, by decide⟩).energy) (xi := (166770169420777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12720 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12720]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12720])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12720) (a := (20853878102543 / 25000000000000 : ℝ)) (b := (161931234639 / 100000000000000 : ℝ)) (q := (1124548898899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12720])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12720]

theorem cert12721_0 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (42037836613343 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281112471581 / 12500000000000 : ℝ))
      (E := (cell12721 ⟨0, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (42037836613343 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281112471581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_1 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (84040704941131 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248903797281 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨1, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (84040704941131 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248903797281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_2 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (84005761580357 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449781549539 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨2, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (84005761580357 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449781549539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_3 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (16794168621577 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248911748407 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨3, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (16794168621577 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248911748407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_4 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (3357437979497 / 4000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449783150029 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨4, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (3357437979497 / 4000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449783150029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_5 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (131095438567 / 156250000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (35139371269 / 1562500000000 : ℝ))
      (E := (cell12721 ⟨5, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (131095438567 / 156250000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (35139371269 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_6 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41933118329171 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281115473709 / 12500000000000 : ℝ))
      (E := (cell12721 ⟨6, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41933118329171 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (281115473709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_7 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83831417378091 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562231946333 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨7, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83831417378091 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562231946333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_8 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (20949155701649 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562232938917 / 25000000000000 : ℝ))
      (E := (cell12721 ⟨8, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (20949155701649 / 25000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (562232938917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_9 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (8376185290851 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248935765923 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨9, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (8376185290851 / 10000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248935765923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_10 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83727107648671 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248939765089 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨10, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83727107648671 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248939765089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_11 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41846193496051 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449788751977 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨11, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41846193496051 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449788751977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_12 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (10457211363001 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124473878389 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨12, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (10457211363001 / 12500000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124473878389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_13 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41811509674887 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248951761989 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨13, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41811509674887 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248951761989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_14 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (41794186147483 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248955781493 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨14, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (41794186147483 / 50000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248955781493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_15 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83553749705329 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449791952571 / 20000000000000 : ℝ))
      (E := (cell12721 ⟨15, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83553749705329 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (449791952571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_16 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (16703830309357 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (89958550787 / 4000000000000 : ℝ))
      (E := (cell12721 ⟨16, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (16703830309357 / 20000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (89958550787 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_17 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83484577785433 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248967807193 / 100000000000000 : ℝ))
      (E := (cell12721 ⟨17, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83484577785433 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (2248967807193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_18 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (83450028387549 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124485881969 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨18, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (83450028387549 / 100000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124485881969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12721_19 : CellCertificate 12721 (886104805931383 / 10000000000000000 : ℝ) (165116086021177 / 100000000000000000 : ℝ) (13340539271123 / 400000000000000 : ℝ)
    (cell12721 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · norm_num [cell12721]
  · have h := gap_lower (n := 12721) (a := (4170775165979 / 5000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124487880521 / 50000000000000 : ℝ))
      (E := (cell12721 ⟨19, by decide⟩).energy) (xi := (13340539271123 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12721 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12721]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12721])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12721) (a := (4170775165979 / 5000000000000 : ℝ)) (b := (161918350471 / 100000000000000 : ℝ)) (q := (1124487880521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12721])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12721]

theorem cert12722_0 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (84075658148577 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562194441779 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨0, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (84075658148577 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562194441779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_1 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (16808138036451 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (14054885993 / 625000000000 : ℝ))
      (E := (cell12722 ⟨1, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (16808138036451 / 20000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (14054885993 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_2 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (84005747140263 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248785792869 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨2, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (84005747140263 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248785792869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_3 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83970828986121 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248789762211 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨3, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83970828986121 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248789762211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_4 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83935935683543 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281099223901 / 12500000000000 : ℝ))
      (E := (cell12722 ⟨4, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83935935683543 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281099223901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_5 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83901067196431 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112439888619 / 5000000000000 : ℝ))
      (E := (cell12722 ⟨5, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83901067196431 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (112439888619 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_6 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41933111744439 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248801771659 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨6, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41933111744439 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248801771659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_7 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41915702262583 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56220144921 / 2500000000000 : ℝ))
      (E := (cell12722 ⟨7, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41915702262583 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56220144921 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_8 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20949152567441 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281101224683 / 12500000000000 : ℝ))
      (E := (cell12722 ⟨8, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20949152567441 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (281101224683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_9 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41880920343663 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248813780751 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨9, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41880920343663 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248813780751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_10 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83727095742693 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248817753667 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨10, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83727095742693 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248817753667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_11 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41846187700443 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248821781 / 100000000000 : ℝ))
      (E := (cell12722 ⟨11, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41846187700443 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248821781 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_12 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (10457209953389 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124412876551 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨12, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (10457209953389 / 12500000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124412876551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_13 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41811504193379 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124414896177 / 50000000000000 : ℝ))
      (E := (cell12722 ⟨13, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41811504193379 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (1124414896177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_14 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (8358836164539 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56220844713 / 2500000000000 : ℝ))
      (E := (cell12722 ⟨14, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (8358836164539 / 10000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (56220844713 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_15 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (83553739368753 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248837805423 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨15, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (83553739368753 / 100000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248837805423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_16 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20879785380693 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562210447589 / 25000000000000 : ℝ))
      (E := (cell12722 ⟨16, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20879785380693 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (562210447589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_17 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (41742284036773 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248845806699 / 100000000000000 : ℝ))
      (E := (cell12722 ⟨17, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (41742284036773 / 50000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (2248845806699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_18 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (1669000379747 / 2000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (137258899 / 6103515625 : ℝ))
      (E := (cell12722 ⟨18, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (1669000379747 / 2000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (137258899 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12722_19 : CellCertificate 12722 (110759619973063 / 1250000000000000 : ℝ) (1651031029775639 / 1000000000000000000 : ℝ) (83371657274359 / 2500000000000000 : ℝ)
    (cell12722 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · norm_num [cell12722]
  · have h := gap_lower (n := 12722) (a := (20853873557659 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (224885377859 / 10000000000000 : ℝ))
      (E := (cell12722 ⟨19, by decide⟩).energy) (xi := (83371657274359 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12722 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12722]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12722])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12722) (a := (20853873557659 / 25000000000000 : ℝ)) (b := (80952734183 / 50000000000000 : ℝ)) (q := (224885377859 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12722])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12722]

theorem cert12723_0 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (84075643072843 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (281081976837 / 12500000000000 : ℝ))
      (E := (cell12723 ⟨0, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (84075643072843 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (281081976837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_1 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (42020337712857 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248659831491 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨1, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (42020337712857 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248659831491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_2 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (328147393369 / 390625000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (89946553337 / 4000000000000 : ℝ))
      (E := (cell12723 ⟨2, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (328147393369 / 390625000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (89946553337 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_3 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16794162973323 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124333914659 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨3, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16794162973323 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124333914659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_4 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83935921881879 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248671827733 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨4, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83935921881879 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248671827733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_5 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83901053712161 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124337918487 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨5, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83901053712161 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124337918487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_6 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (16773242064311 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248679807139 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨6, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (16773242064311 / 20000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248679807139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_7 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (10478923959293 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248683803927 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨7, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (10478923959293 / 12500000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248683803927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_8 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20949149433749 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1756787371 / 78125000000 : ℝ))
      (E := (cell12723 ⟨8, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20949149433749 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1756787371 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_9 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83761828468169 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248691791237 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨9, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83761828468169 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248691791237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_10 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41863541919351 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248695795989 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨10, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41863541919351 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248695795989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_11 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (4184618190581 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562174949463 / 25000000000000 : ℝ))
      (E := (cell12723 ⟨11, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (4184618190581 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562174949463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_12 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (653575534001 / 781250000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124351901647 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨12, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (653575534001 / 781250000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124351901647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_13 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (5226437339101 / 6250000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562176954633 / 25000000000000 : ℝ))
      (E := (cell12723 ⟨13, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (5226437339101 / 6250000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (562176954633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_14 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83588350997649 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248711791401 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨14, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83588350997649 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248711791401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_15 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (3342149161359 / 4000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248715843883 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨15, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (3342149161359 / 4000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248715843883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_16 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (83519131500519 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248719806967 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨16, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (83519131500519 / 100000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248719806967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_17 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (4174227918169 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (35136309409 / 1562500000000 : ℝ))
      (E := (cell12723 ⟨17, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (4174227918169 / 5000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (35136309409 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_18 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (20862502397209 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124363917251 / 50000000000000 : ℝ))
      (E := (cell12723 ⟨18, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (20862502397209 / 25000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (1124363917251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12723_19 : CellCertificate 12723 (110756139729977 / 1250000000000000 : ℝ) (1650901219754981 / 1000000000000000000 : ℝ) (333459780798473 / 10000000000000000 : ℝ)
    (cell12723 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · norm_num [cell12723]
  · have h := gap_lower (n := 12723) (a := (41707742571669 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248731850443 / 100000000000000 : ℝ))
      (E := (cell12723 ⟨19, by decide⟩).energy) (xi := (333459780798473 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12723 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12723]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12723])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12723) (a := (41707742571669 / 50000000000000 : ℝ)) (b := (80946294163 / 50000000000000 : ℝ)) (q := (2248731850443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12723])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12723]

theorem cert12724_0 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (2101890699987 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124266928791 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨0, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (2101890699987 / 2500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124266928791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_1 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (84040660671507 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248537899447 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨1, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (84040660671507 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248537899447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_2 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (84005718266961 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562135467341 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨2, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (84005718266961 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562135467341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_3 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16794160149873 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248545891849 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨3, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16794160149873 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248545891849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_4 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83935908082433 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (56213746493 / 2500000000000 : ℝ))
      (E := (cell12724 ⟨4, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83935908082433 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (56213746493 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_5 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83901040230071 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248553897071 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨5, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83901040230071 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248553897071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_6 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83866197156373 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449711579223 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨6, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83866197156373 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449711579223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_7 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (10478922353203 / 12500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562140466143 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨7, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (10478922353203 / 12500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562140466143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_8 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83796585202293 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449713173583 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨8, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83796585202293 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449713173583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_9 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41880908125519 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449713971081 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨9, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41880908125519 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449713971081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_10 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (837270719367 / 1000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (281071736507 / 12500000000000 : ℝ))
      (E := (cell12724 ⟨10, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (837270719367 / 1000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (281071736507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_11 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83692352224303 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (70268058391 / 3125000000000 : ℝ))
      (E := (cell12724 ⟨11, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83692352224303 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (70268058391 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_12 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (5228603567441 / 6250000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248581907357 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨12, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (5228603567441 / 6250000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248581907357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_13 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (83622986466347 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449717179729 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨13, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (83622986466347 / 100000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449717179729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_14 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (326516954499 / 390625000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248589906417 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨14, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (326516954499 / 390625000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248589906417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_15 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (16710743740199 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562148469559 / 25000000000000 : ℝ))
      (E := (cell12724 ⟨15, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (16710743740199 / 20000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (562148469559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_16 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (3340764859201 / 4000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (22485978777 / 1000000000000 : ℝ))
      (E := (cell12724 ⟨16, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (3340764859201 / 4000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (22485978777 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_17 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (10435568581867 / 12500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449720382009 / 20000000000000 : ℝ))
      (E := (cell12724 ⟨17, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (10435568581867 / 12500000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (449720382009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_18 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41725000096003 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248605863799 / 100000000000000 : ℝ))
      (E := (cell12724 ⟨18, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41725000096003 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (2248605863799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

theorem cert12724_19 : CellCertificate 12724 (35440851203853 / 400000000000000 : ℝ) (825385715072491 / 500000000000000000 : ℝ) (333432936880023 / 10000000000000000 : ℝ)
    (cell12724 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · norm_num [cell12724]
  · have h := gap_lower (n := 12724) (a := (41707738028843 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124304959173 / 50000000000000 : ℝ))
      (E := (cell12724 ⟨19, by decide⟩).energy) (xi := (333432936880023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12724 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12724]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12724])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12724) (a := (41707738028843 / 50000000000000 : ℝ)) (b := (161879710349 / 100000000000000 : ℝ)) (q := (1124304959173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12724])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12724]

end BstLean.Part268
