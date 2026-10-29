import BstLean.Part268CellShard26Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13000_0 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (84071556509117 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443200718977 / 20000000000000 : ℝ))
      (E := (cell13000 ⟨0, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (84071556509117 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443200718977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_1 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (10504583380437 / 12500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216007643 / 100000000000 : ℝ))
      (E := (cell13000 ⟨1, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (10504583380437 / 12500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216007643 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_2 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (84001802391407 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110800581493 / 5000000000000 : ℝ))
      (E := (cell13000 ⟨2, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (84001802391407 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110800581493 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_3 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41983481258307 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216015621681 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨3, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41983481258307 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216015621681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_4 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41966073691537 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108009813291 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨4, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41966073691537 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108009813291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_5 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (8389735695493 / 10000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (221602365243 / 10000000000000 : ℝ))
      (E := (cell13000 ⟨5, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (8389735695493 / 10000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (221602365243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_6 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20965647799129 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554006912213 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨6, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20965647799129 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554006912213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_7 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83827850072351 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110801584057 / 5000000000000 : ℝ))
      (E := (cell13000 ⟨7, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83827850072351 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110801584057 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_8 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (4189656677357 / 5000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443207128069 / 20000000000000 : ℝ))
      (E := (cell13000 ⟨8, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (4189656677357 / 5000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443207128069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_9 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83758441585773 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216039649279 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨9, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83758441585773 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216039649279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_10 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41861887076661 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108021828237 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨10, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41861887076661 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108021828237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_11 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41844565607521 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108023834107 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨11, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41844565607521 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108023834107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_12 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (5228407046023 / 6250000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216051690537 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨12, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (5228407046023 / 6250000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216051690537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_13 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (16723983736583 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216055671091 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨13, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (16723983736583 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216055671091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_14 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83585349020477 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554014918379 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨14, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83585349020477 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554014918379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_15 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (5221925232189 / 6250000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554015925779 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨15, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (5221925232189 / 6250000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554015925779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_16 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83516282732703 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108033853367 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨16, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83516282732703 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108033853367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_17 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20870446509959 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216071747353 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨17, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20870446509959 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216071747353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_18 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83447313602919 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554018928257 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨18, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83447313602919 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554018928257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_19 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41706432694311 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216079724519 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨19, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41706432694311 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216079724519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13001_0 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (84071542072041 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553972336149 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨0, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (84071542072041 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553972336149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_1 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (84036652612829 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553973346809 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨1, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (84036652612829 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553973346809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_2 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (84001787967143 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553974342167 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨2, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (84001787967143 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553974342167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_3 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20991737024687 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107950706509 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨3, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20991737024687 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107950706509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_4 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (209830332429 / 250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (4327940259 / 195312500000 : ℝ))
      (E := (cell13001 ⟨4, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (209830332429 / 250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (4327940259 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_5 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41948671274921 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443181875047 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨5, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41948671274921 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443181875047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_6 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83862576797809 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553978356099 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨6, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83862576797809 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553978356099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_7 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83827835680019 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215917393511 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨7, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83827835680019 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215917393511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_8 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83793119161177 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443184281119 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨8, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83793119161177 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443184281119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_9 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83758427206173 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107962704727 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨9, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83758427206173 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107962704727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_10 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (1046546997251 / 1250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215929411619 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨10, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (1046546997251 / 1250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215929411619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_11 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (10461139606019 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215933418377 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨11, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (10461139606019 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215933418377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_12 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (5228406148489 / 6250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553984358941 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨12, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (5228406148489 / 6250000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553984358941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_13 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (10452488041089 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553985367393 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨13, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (10452488041089 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553985367393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_14 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83585334672609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107972733589 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨14, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83585334672609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107972733589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_15 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41775394686743 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443189886763 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨15, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41775394686743 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443189886763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_16 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83516268397489 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107976745449 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨16, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83516268397489 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107976745449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_17 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83481771710941 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215957468601 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨17, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83481771710941 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215957468601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_18 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41723649640169 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (55399037197 / 2500000000000 : ℝ))
      (E := (cell13001 ⟨18, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41723649640169 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (55399037197 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_19 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20853212768087 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107982747393 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨19, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20853212768087 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107982747393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13002_0 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (21017881909297 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107887573883 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨0, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (21017881909297 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107887573883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_1 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (16807327636877 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553944781773 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨1, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (16807327636877 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553944781773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_2 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (42000886772551 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107891580491 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨2, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (42000886772551 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107891580491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_3 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83966933683103 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443157428413 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨3, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83966933683103 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443157428413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_4 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41966059281173 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443158238851 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨4, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41966059281173 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443158238851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_5 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83897328146973 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215795151619 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨5, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83897328146973 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215795151619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_6 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83862562401319 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443159839113 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨6, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83862562401319 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443159839113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_7 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83827821289903 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221580315951 / 10000000000000 : ℝ))
      (E := (cell13002 ⟨7, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83827821289903 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221580315951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_8 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83793104777429 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276975895809 / 12500000000000 : ℝ))
      (E := (cell13002 ⟨8, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83793104777429 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276975895809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_9 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20939603207197 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443162244661 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨9, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20939603207197 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443162244661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_10 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83723745409051 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443163044093 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨10, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83723745409051 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443163044093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_11 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41844551241737 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443163844453 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨11, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41844551241737 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443163844453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_12 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20913621004373 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (110791161737 / 5000000000000 : ℝ))
      (E := (cell13002 ⟨12, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20913621004373 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (110791161737 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_13 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (1045248624709 / 1250000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215827205539 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨13, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (1045248624709 / 1250000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215827205539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_14 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83585320326951 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276978907059 / 12500000000000 : ℝ))
      (E := (cell13002 ⟨14, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83585320326951 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276978907059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_15 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83550775034157 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215835218337 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨15, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83550775034157 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215835218337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_16 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20879063516121 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107919635347 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨16, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20879063516121 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107919635347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_17 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83481757384253 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (55396081093 / 2500000000000 : ℝ))
      (E := (cell13002 ⟨17, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83481757384253 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (55396081093 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_18 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41723642479981 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (8655653353 / 390625000000 : ℝ))
      (E := (cell13002 ⟨18, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41723642479981 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (8655653353 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_19 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (2085320918957 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138490703793 / 6250000000000 : ℝ))
      (E := (cell13002 ⟨19, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (2085320918957 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138490703793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13003_0 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (84071513204559 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215660946557 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨0, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (84071513204559 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215660946557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_1 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (84036623758163 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276958122287 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨1, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (84036623758163 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276958122287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_2 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (84001759125281 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55391723723 / 2500000000000 : ℝ))
      (E := (cell13003 ⟨2, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (84001759125281 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55391723723 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_3 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41983459634839 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215672982557 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨3, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41983459634839 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215672982557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_4 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (8393210415531 / 10000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215676971529 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨4, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (8393210415531 / 10000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215676971529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_5 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41948656873161 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215680981587 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨5, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41948656873161 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215680981587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_6 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83862548007047 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55392124059 / 2500000000000 : ℝ))
      (E := (cell13003 ⟨6, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83862548007047 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55392124059 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_7 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83827806902003 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215688979141 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨7, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83827806902003 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215688979141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_8 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (10474136299487 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443138596201 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨8, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (10474136299487 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443138596201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_9 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (5234899903351 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215696974737 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨9, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (5234899903351 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215696974737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_10 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (20930932760059 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107850512471 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨10, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (20930932760059 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107850512471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_11 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83689088121009 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276963127723 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨11, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83689088121009 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276963127723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_12 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83654469661371 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (44314180587 / 2000000000000 : ℝ))
      (E := (cell13003 ⟨12, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83654469661371 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (44314180587 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_13 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41809937813469 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443142599057 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨13, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41809937813469 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443142599057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_14 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83585305983503 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215717041399 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨14, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83585305983503 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215717041399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_15 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (20887690174259 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443144211337 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨15, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (20887690174259 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443144211337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_16 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16703247946737 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (138482815383 / 6250000000000 : ℝ))
      (E := (cell13003 ⟨16, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16703247946737 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (138482815383 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_17 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (20870435764943 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215729072713 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨17, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (20870435764943 / 25000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215729072713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_18 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (651931801889 / 781250000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107866541377 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨18, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (651931801889 / 781250000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107866541377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_19 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (5213301402901 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215737080513 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨19, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (5213301402901 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215737080513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13004_0 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (10508937346769 / 12500000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221554674097 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨0, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (10508937346769 / 12500000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221554674097 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_1 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (42018304667081 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215550767259 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨1, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (42018304667081 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215550767259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_2 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (84001744707681 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (69236087199 / 3125000000000 : ℝ))
      (E := (cell13004 ⟨2, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (84001744707681 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (69236087199 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_3 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83966904858473 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107779380381 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨3, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83966904858473 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107779380381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_4 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41966044875247 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215562802359 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨4, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41966044875247 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215562802359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_5 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83897299347889 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215566807179 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨5, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83897299347889 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215566807179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_6 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83862533614991 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107785391381 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨6, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83862533614991 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107785391381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_7 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83827792516319 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107787397199 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨7, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83827792516319 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107787397199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_8 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41896538008289 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107789395583 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨8, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41896538008289 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107789395583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_9 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83758384080659 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215582837897 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨9, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83758384080659 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215582837897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_10 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83723716673633 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44311736501 / 2000000000000 : ℝ))
      (E := (cell13004 ⟨10, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83723716673633 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44311736501 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_11 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (16737814752151 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443118163387 / 20000000000000 : ℝ))
      (E := (cell13004 ⟨11, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (16737814752151 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443118163387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_12 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83654455307461 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221559481959 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨12, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83654455307461 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221559481959 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_13 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41809930639683 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107799419403 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨13, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41809930639683 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107799419403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_14 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83585291642263 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (17309397501 / 781250000000 : ℝ))
      (E := (cell13004 ⟨14, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83585291642263 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (17309397501 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_15 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (20887686590531 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553901708119 / 25000000000000 : ℝ))
      (E := (cell13004 ⟨15, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (20887686590531 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553901708119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_16 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41758112702547 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215610875411 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨16, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41758112702547 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215610875411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_17 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83481728737497 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107807448671 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨17, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83481728737497 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107807448671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_18 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83447256325827 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215618902777 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨18, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83447256325827 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215618902777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_19 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (16682561627351 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215622895977 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨19, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (16682561627351 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215622895977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13005_0 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (84071484345967 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107716294423 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨0, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (84071484345967 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107716294423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_1 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (42018297456191 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215436609711 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨1, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (42018297456191 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215436609711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_2 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (84001730292301 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215440627441 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨2, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (84001730292301 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215440627441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_3 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41983445224743 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443088930083 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨3, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41983445224743 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443088930083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_4 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16786415069579 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107724314409 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨4, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16786415069579 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107724314409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_5 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83897284951673 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (5538631571 / 250000000000 : ℝ))
      (E := (cell13005 ⟨5, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83897284951673 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (5538631571 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_6 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83862519225151 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107728328387 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨6, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83862519225151 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107728328387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_7 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (1676555562657 / 2000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221546066329 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨7, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (1676555562657 / 2000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221546066329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_8 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41896530819737 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443092930997 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨8, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41896530819737 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443092930997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_9 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41879184854957 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215468638641 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨9, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41879184854957 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215468638641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_10 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41861851154621 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (138467042429 / 6250000000000 : ℝ))
      (E := (cell13005 ⟨10, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41861851154621 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (138467042429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_11 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83689059402713 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276934583227 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨11, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83689059402713 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276934583227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_12 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41827220477881 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443096132717 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨12, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41827220477881 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443096132717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_13 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (20904961733501 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107742338981 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨13, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (20904961733501 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107742338981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_14 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (1306019957863 / 1562500000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215488714493 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨14, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (1306019957863 / 1562500000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215488714493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_15 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41775366014709 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215492720287 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨15, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41775366014709 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215492720287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_16 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83516211078709 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553874175083 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨16, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83516211078709 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553874175083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_17 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41740857208713 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553875179403 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨17, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41740857208713 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553875179403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_18 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83447242012067 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (55387617961 / 2500000000000 : ℝ))
      (E := (cell13005 ⟨18, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83447242012067 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (55387617961 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_19 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83412793829299 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215508707081 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨19, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83412793829299 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215508707081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13006_0 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (21017867480001 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443063698037 / 20000000000000 : ℝ))
      (E := (cell13006 ⟨0, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (21017867480001 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443063698037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_1 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (84036580492823 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (44306450113 / 2000000000000 : ℝ))
      (E := (cell13006 ⟨1, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (84036580492823 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (44306450113 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_2 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (4200085793957 / 5000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107663259013 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨2, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (4200085793957 / 5000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107663259013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_3 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41983438021359 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215330477783 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨3, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41983438021359 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215330477783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_4 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (16786412189503 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553833627209 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨4, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (16786412189503 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553833627209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_5 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83897270557673 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215338503207 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨5, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83897270557673 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215338503207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_6 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83862504837527 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107671263207 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨6, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83862504837527 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107671263207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_7 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (16765552750319 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553836631953 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨7, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (16765552750319 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553836631953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_8 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (10474130908073 / 12500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107675257217 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨8, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (10474130908073 / 12500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107675257217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_9 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83758355341383 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107677275557 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨9, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83758355341383 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107677275557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_10 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83723687947063 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (221535852831 / 10000000000000 : ℝ))
      (E := (cell13006 ⟨10, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83723687947063 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (221535852831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_11 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83689045046881 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553840642107 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨11, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83689045046881 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553840642107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_12 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (1307100415723 / 1562500000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276920820167 / 12500000000000 : ℝ))
      (E := (cell13006 ⟨12, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (1307100415723 / 1562500000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276920820167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_13 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83619832590849 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215370570899 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨13, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83619832590849 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215370570899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_14 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83585262966409 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215374544493 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨14, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83585262966409 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215374544493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_15 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (2088767942473 / 2500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107689272771 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨15, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (2088767942473 / 2500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107689272771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_16 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (8351619675453 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (69230705597 / 3125000000000 : ℝ))
      (E := (cell13006 ⟨16, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (8351619675453 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (69230705597 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_17 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83481700099561 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553846647939 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨17, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83481700099561 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553846647939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_18 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (8344722770051 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215390588003 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨18, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (8344722770051 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215390588003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_19 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (16682555904809 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443078926079 / 20000000000000 : ℝ))
      (E := (cell13006 ⟨19, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (16682555904809 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443078926079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13007_0 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (84071455496261 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138450274197 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨0, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (84071455496261 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138450274197 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_1 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (21009141518871 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (69225262413 / 3125000000000 : ℝ))
      (E := (cell13007 ⟨1, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (21009141518871 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (69225262413 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_2 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (42000850734099 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (27690155053 / 1250000000000 : ℝ))
      (E := (cell13007 ⟨2, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (42000850734099 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (27690155053 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_3 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83966861638169 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (11076082083 / 500000000000 : ℝ))
      (E := (cell13007 ⟨3, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83966861638169 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (11076082083 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_4 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83932046549351 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443044076897 / 20000000000000 : ℝ))
      (E := (cell13007 ⟨4, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83932046549351 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443044076897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_5 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83897256165889 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215224431601 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨5, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83897256165889 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215224431601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_6 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41931245226059 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107614195843 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨6, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41931245226059 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107614195843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_7 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (16765549874511 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107616193983 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨7, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (16765549874511 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107616193983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_8 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83793032891907 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443047285509 / 20000000000000 : ℝ))
      (E := (cell13007 ⟨8, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83793032891907 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443047285509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_9 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83758340975063 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107620200587 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨9, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83758340975063 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107620200587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_10 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (10465459198387 / 12500000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443048886293 / 20000000000000 : ℝ))
      (E := (cell13007 ⟨10, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (10465459198387 / 12500000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443048886293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_11 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (4184451534663 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553812116669 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨11, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (4184451534663 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553812116669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_12 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83654412258991 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553813113681 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨12, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83654412258991 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553813113681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_13 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (5226238640619 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215256459473 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨13, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (5226238640619 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215256459473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_14 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (5224078039487 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215260486469 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨14, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (5224078039487 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215260486469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_15 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83550703370627 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215264482821 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨15, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83550703370627 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215264482821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_16 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (20879045608139 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107634226759 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨16, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (20879045608139 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107634226759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_17 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (834816857839 / 1000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215272461543 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨17, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (834816857839 / 1000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215272461543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_18 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (20861803347789 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215276511471 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨18, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (20861803347789 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215276511471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_19 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83412765220993 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553820122767 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨19, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83412765220993 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553820122767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13008_0 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (84071441074739 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215090279743 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨0, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (84071441074739 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215090279743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_1 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16807310332073 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (276886785551 / 12500000000000 : ℝ))
      (E := (cell13008 ⟨1, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16807310332073 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (276886785551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_2 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (3360067482379 / 4000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27039774 / 1220703125 : ℝ))
      (E := (cell13008 ⟨2, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (3360067482379 / 4000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27039774 / 1220703125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_3 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (20991711808959 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (138443893321 / 6250000000000 : ℝ))
      (E := (cell13008 ⟨3, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (20991711808959 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (138443893321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_4 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83932032153403 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (69222072303 / 3125000000000 : ℝ))
      (E := (cell13008 ⟨4, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83932032153403 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (69222072303 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_5 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83897241776321 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215110297667 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨5, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83897241776321 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215110297667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_6 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83862476068923 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215114310569 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨6, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83862476068923 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215114310569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_7 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (5239233437233 / 6250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27688979497 / 1250000000000 : ℝ))
      (E := (cell13008 ⟨7, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (5239233437233 / 6250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27688979497 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_8 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83793018521443 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215122336287 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨8, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83793018521443 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215122336287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_9 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16751665322191 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215126362967 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨9, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16751665322191 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215126362967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_10 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41861829614669 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443026066051 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨10, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41861829614669 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443026066051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_11 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (10461127042731 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27689179507 / 1250000000000 : ℝ))
      (E := (cell13008 ⟨11, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (10461127042731 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (27689179507 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_12 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83654397913919 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215138343747 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨12, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83654397913919 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215138343747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_13 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41809901955583 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (553785585921 / 25000000000000 : ℝ))
      (E := (cell13008 ⟨13, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41809901955583 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (553785585921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_14 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83585234299383 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215146365913 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨14, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83585234299383 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215146365913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_15 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83550689044541 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107575178773 / 50000000000000 : ℝ))
      (E := (cell13008 ⟨15, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83550689044541 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107575178773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_16 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83516168112787 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443030876357 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨16, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83516168112787 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443030876357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_17 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83481671470443 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (276894798151 / 12500000000000 : ℝ))
      (E := (cell13008 ⟨17, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83481671470443 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (276894798151 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_18 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41723599542003 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215162430579 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨18, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41723599542003 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215162430579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_19 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (5213296932509 / 6250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215166405667 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨19, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (5213296932509 / 6250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215166405667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13009_0 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (42035713327719 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214976225801 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨0, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (42035713327719 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214976225801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_1 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10504567155933 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553745056273 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨1, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10504567155933 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553745056273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_2 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8400167265297 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214984221437 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨2, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8400167265297 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214984221437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_3 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (83966832835721 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553747055803 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨3, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (83966832835721 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553747055803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_4 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10491502219959 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214992238539 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨4, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10491502219959 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2214992238539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_5 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10487153423621 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (27687453441 / 1250000000000 : ℝ))
      (E := (cell13009 ⟨5, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10487153423621 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (27687453441 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_6 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (83862461687943 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107500141533 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨6, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (83862461687943 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107500141533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_7 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16765544124223 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215004269183 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨7, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16765544124223 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215004269183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_8 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8379300415319 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553752074673 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨8, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8379300415319 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553752074673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_9 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41879156124529 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107506131173 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨9, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41879156124529 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107506131173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_10 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (1308181951153 / 1562500000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443003256551 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨10, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (1308181951153 / 1562500000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443003256551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_11 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16737800398529 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107510154089 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨11, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16737800398529 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107510154089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_12 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16730876714211 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215024286531 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨12, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16730876714211 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215024286531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_13 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16723957914927 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107514140839 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨13, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16723957914927 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107514140839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_14 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (4179260998459 / 5000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107516149583 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨14, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (4179260998459 / 5000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107516149583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_15 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (4177533736033 / 5000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443007268859 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨15, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (4177533736033 / 5000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443007268859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_16 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41758076897611 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443008061139 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨16, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41758076897611 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443008061139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_17 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8348165715919 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (4326258521 / 195312500000 : ℝ))
      (E := (cell13009 ⟨17, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8348165715919 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (4326258521 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_18 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41723592389529 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553762086333 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨18, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41723592389529 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553762086333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_19 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10426592077687 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443010474839 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨19, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10426592077687 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443010474839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13010_0 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16814282447671 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221486216749 / 10000000000000 : ℝ))
      (E := (cell13010 ⟨0, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16814282447671 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221486216749 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_1 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (42018261418391 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214866219271 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨1, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (42018261418391 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214866219271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_2 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (84001658248683 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214870210311 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨2, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (84001658248683 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214870210311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_3 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41983409218911 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214874206831 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨3, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41983409218911 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214874206831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_4 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (20983000842039 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553719554237 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨4, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (20983000842039 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553719554237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_5 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (8389721300383 / 10000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214882248527 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨5, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (8389721300383 / 10000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214882248527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_6 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (10482805913647 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214886251197 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨6, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (10482805913647 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214886251197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_7 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41913853124357 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107445116123 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨7, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41913853124357 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107445116123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_8 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83792989787149 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107447128367 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨8, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83792989787149 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107447128367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_9 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (20939574472343 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214898273463 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨9, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (20939574472343 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214898273463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_10 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41861815260227 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107451115447 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨10, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41861815260227 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107451115447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_11 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83688987645651 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553726562859 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨11, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83688987645651 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553726562859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_12 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41827184615199 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (88596411323 / 4000000000000 : ℝ))
      (E := (cell13010 ⟨12, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41827184615199 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (88596411323 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_13 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83619775240311 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107457136729 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨13, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83619775240311 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107457136729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_14 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41792602820591 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214918286229 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨14, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41792602820591 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214918286229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_15 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83550660398983 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (138432641781 / 6250000000000 : ℝ))
      (E := (cell13010 ⟨15, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83550660398983 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (138432641781 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_16 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83516139479861 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107463141731 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨16, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83516139479861 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107463141731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_17 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83481642850139 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (442986055541 / 20000000000000 : ℝ))
      (E := (cell13010 ⟨17, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83481642850139 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (442986055541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_18 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83447170476311 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (276866789249 / 12500000000000 : ℝ))
      (E := (cell13010 ⟨18, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83447170476311 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (276866789249 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_19 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83412722325049 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221493833837 / 10000000000000 : ℝ))
      (E := (cell13010 ⟨19, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83412722325049 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221493833837 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13011_0 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (21017849455873 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107374081323 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨0, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (21017849455873 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107374081323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_1 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (42018254214159 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107376104539 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨1, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (42018254214159 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107376104539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_2 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (21000410961653 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214756194817 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨2, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (21000410961653 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214756194817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_3 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (4198340202107 / 5000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (13842251163 / 625000000000 : ℝ))
      (E := (cell13011 ⟨3, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (4198340202107 / 5000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (13842251163 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_4 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (10491498622357 / 12500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553691047747 / 25000000000000 : ℝ))
      (E := (cell13011 ⟨4, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (10491498622357 / 12500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553691047747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_5 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (16779439724181 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214768217407 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨5, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (16779439724181 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214768217407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_6 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41931216466311 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107386107481 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨6, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41931216466311 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107386107481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_7 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (3353107675141 / 4000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214776190943 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨7, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (3353107675141 / 4000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214776190943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_8 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (2094824385583 / 2500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221478021041 / 10000000000000 : ℝ))
      (E := (cell13011 ⟨8, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (2094824385583 / 2500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221478021041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_9 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (10469785441487 / 12500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442956844433 / 20000000000000 : ℝ))
      (E := (cell13011 ⟨9, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (10469785441487 / 12500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442956844433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_10 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41861808084663 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (276848529093 / 12500000000000 : ℝ))
      (E := (cell13011 ⟨10, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41861808084663 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (276848529093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_11 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (16737794660173 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214792248429 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨11, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (16737794660173 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214792248429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_12 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83654354891949 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107398137629 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨12, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83654354891949 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107398137629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_13 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83619760908193 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107400130439 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨13, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83619760908193 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107400130439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_14 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (8358519131539 / 10000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214804268931 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨14, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (8358519131539 / 10000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214804268931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_15 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83550646079511 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214808246529 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨15, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83550646079511 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214808246529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_16 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (5219757822919 / 6250000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214812256871 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨16, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (5219757822919 / 6250000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214812256871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_17 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (8348162854329 / 10000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (276852038097 / 12500000000000 : ℝ))
      (E := (cell13011 ⟨17, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (8348162854329 / 10000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (276852038097 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_18 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41723578087883 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442964055659 / 20000000000000 : ℝ))
      (E := (cell13011 ⟨18, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41723578087883 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442964055659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_19 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41706354015401 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221482429819 / 10000000000000 : ℝ))
      (E := (cell13011 ⟨19, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41706354015401 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221482429819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13012_0 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (84071383410847 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (88585368451 / 4000000000000 : ℝ))
      (E := (cell13012 ⟨0, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (84071383410847 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (88585368451 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_1 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (84036494022071 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107319097259 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨1, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (84036494022071 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107319097259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_2 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (42000814723379 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107321087477 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨2, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (42000814723379 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107321087477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_3 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (2623962176521 / 3125000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107323109437 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨3, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (2623962176521 / 3125000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107323109437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_4 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83931974591769 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214650218599 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨4, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83931974591769 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214650218599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_5 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (16779436848039 / 20000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214654239879 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨5, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (16779436848039 / 20000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214654239879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_6 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83862418558281 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442931646469 / 20000000000000 : ℝ))
      (E := (cell13012 ⟨6, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83862418558281 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442931646469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_7 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20956919377637 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107331101641 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨7, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20956919377637 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107331101641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_8 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83792961061701 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (276833277219 / 12500000000000 : ℝ))
      (E := (cell13012 ⟨8, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83792961061701 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (276833277219 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_9 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83758269176629 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214670224559 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨9, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83758269176629 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214670224559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_10 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83723601820407 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107337115117 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨10, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83723601820407 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107337115117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_11 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83688958958287 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214678241063 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨11, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83688958958287 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214678241063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_12 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83654340555707 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214682263083 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨12, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83654340555707 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214682263083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_13 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83619746578281 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214686243941 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨13, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83619746578281 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214686243941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_14 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41792588495901 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214690247279 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨14, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41792588495901 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214690247279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_15 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83550631762243 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107347139199 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨15, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83550631762243 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107347139199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_16 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83516110855749 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107349142071 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨16, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83516110855749 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107349142071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_17 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83481614238643 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214702269257 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨17, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83481614238643 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214702269257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_18 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41723570938711 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553676574127 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨18, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41723570938711 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553676574127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_19 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (16682538747751 / 20000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (276838788993 / 12500000000000 : ℝ))
      (E := (cell13012 ⟨19, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (16682538747751 / 20000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (276838788993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13013_0 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (84071369000419 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (34601878089 / 1562500000000 : ℝ))
      (E := (cell13013 ⟨0, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (84071369000419 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (34601878089 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_1 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (42018239809021 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107262116727 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨1, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (42018239809021 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107262116727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_2 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (525010094057 / 625000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107264104307 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨2, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (525010094057 / 625000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107264104307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_3 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (4198338762871 / 5000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214532247303 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨3, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (4198338762871 / 5000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214532247303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_4 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83931960206897 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442907248369 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨4, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83931960206897 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442907248369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_5 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83897169861697 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553635064497 / 25000000000000 : ℝ))
      (E := (cell13013 ⟨5, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83897169861697 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553635064497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_6 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83862404186151 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107272122683 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨6, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83862404186151 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107272122683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_7 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83827663144781 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (138409266829 / 6250000000000 : ℝ))
      (E := (cell13013 ⟨7, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83827663144781 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (138409266829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_8 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20948236675573 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107276139381 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨8, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20948236675573 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107276139381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_9 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20939563705893 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214556280643 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨9, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20939563705893 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214556280643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_10 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (16744717494739 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (13841001759 / 625000000000 : ℝ))
      (E := (cell13013 ⟨10, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (16744717494739 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (13841001759 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_11 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20922236154479 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107282143719 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨11, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20922236154479 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107282143719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_12 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83654326221671 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214568304673 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨12, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83654326221671 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214568304673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_13 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41809866125287 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276821535099 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨13, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41809866125287 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276821535099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_14 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83585162670419 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214576279439 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨14, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83585162670419 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214576279439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_15 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83550617447177 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107290152957 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨15, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83550617447177 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107290152957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_16 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20879024136749 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110729215353 / 5000000000000 : ℝ))
      (E := (cell13013 ⟨16, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20879024136749 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110729215353 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_17 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41740799968099 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110729417293 / 5000000000000 : ℝ))
      (E := (cell13013 ⟨17, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41740799968099 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110729417293 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_18 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41723563790639 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214592310369 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨18, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41723563790639 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214592310369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_19 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83412679448907 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214596321347 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨19, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83412679448907 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214596321347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13014_0 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (8407135459221 / 10000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214406295429 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨0, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (8407135459221 / 10000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214406295429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_1 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (21009116304057 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276801283503 / 12500000000000 : ℝ))
      (E := (cell13014 ⟨1, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (21009116304057 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276801283503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_2 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (84001600653697 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107207147897 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨2, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (84001600653697 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107207147897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_3 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41983380434191 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214418271367 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨3, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41983380434191 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214418271367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_4 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41965972912119 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110721115933 / 5000000000000 : ℝ))
      (E := (cell13014 ⟨4, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41965972912119 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110721115933 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_5 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83897155485411 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442885254347 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨5, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83897155485411 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442885254347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_6 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41931194908117 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214430312003 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨6, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41931194908117 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214430312003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_7 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41913824390613 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553608582721 / 25000000000000 : ℝ))
      (E := (cell13014 ⟨7, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41913824390613 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553608582721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_8 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (20948233086273 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214438335411 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨8, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (20948233086273 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214438335411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_9 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83758240472723 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (138402645773 / 6250000000000 : ℝ))
      (E := (cell13014 ⟨9, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83758240472723 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (138402645773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_10 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83723573129191 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214446328287 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨10, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83723573129191 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214446328287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_11 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (10461116284969 / 12500000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214450329453 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨11, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (10461116284969 / 12500000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214450329453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_12 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (1045678898623 / 1250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442890868381 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨12, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (1045678898623 / 1250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442890868381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_13 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83619717925071 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276807296429 / 12500000000000 : ℝ))
      (E := (cell13014 ⟨13, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83619717925071 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276807296429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_14 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83585148351239 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214462365411 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨14, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83585148351239 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214462365411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_15 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (16710120626863 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442893277453 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨15, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (16710120626863 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442893277453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_16 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (16703216448089 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107235191919 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨16, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (16703216448089 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107235191919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_17 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83481585635953 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214474359873 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨17, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83481585635953 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214474359873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_18 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41723556643667 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214478378139 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨18, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41723556643667 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214478378139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_19 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41706332580629 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553620596171 / 25000000000000 : ℝ))
      (E := (cell13014 ⟨19, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41706332580629 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553620596171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13015_0 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (84071340186217 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553573082739 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨0, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (84071340186217 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553573082739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_1 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (84036450816631 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214296356091 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨1, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (84036450816631 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214296356091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_2 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (8400158626049 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214300378609 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨2, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (8400158626049 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214300378609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_3 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41983373240779 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214304348977 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨3, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41983373240779 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214304348977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_4 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83931931443793 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276788548889 / 12500000000000 : ℝ))
      (E := (cell13015 ⟨4, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83931931443793 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276788548889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_5 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41948570555669 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214312397033 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨5, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41948570555669 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214312397033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_6 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83862375448527 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55357909357 / 2500000000000 : ℝ))
      (E := (cell13015 ⟨6, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83862375448527 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55357909357 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_7 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (2095690860497 / 2500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (138395024259 / 6250000000000 : ℝ))
      (E := (cell13015 ⟨7, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (2095690860497 / 2500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (138395024259 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_8 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41896458995051 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (22143243877 / 1000000000000 : ℝ))
      (E := (cell13015 ⟨8, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41896458995051 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (22143243877 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_9 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41879113062041 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107164189867 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨9, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41879113062041 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107164189867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_10 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16744711757379 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (44286648577 / 2000000000000 : ℝ))
      (E := (cell13015 ⟨10, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16744711757379 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (44286648577 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_11 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41844457971897 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (221433642521 / 10000000000000 : ℝ))
      (E := (cell13015 ⟨11, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41844457971897 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (221433642521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_12 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16730859512043 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107170216451 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨12, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16730859512043 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107170216451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_13 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83619703601773 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553586114429 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨13, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83619703601773 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553586114429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_14 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83585134034263 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214348447029 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨14, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83585134034263 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214348447029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_15 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16710117764731 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214352464263 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨15, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16710117764731 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214352464263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_16 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (2609877123003 / 3125000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214356456263 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨16, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (2609877123003 / 3125000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214356456263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_17 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83481571337909 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214360486011 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨17, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83481571337909 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214360486011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_18 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (8344709899559 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107182220779 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨18, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (8344709899559 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107182220779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_19 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (2606645339869 / 3125000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442873700391 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨19, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (2606645339869 / 3125000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442873700391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13016_0 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (84071325782441 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107089209979 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨0, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (84071325782441 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107089209979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_1 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (84036436419249 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442836487959 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨1, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (84036436419249 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442836487959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_2 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (10500196483687 / 12500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214186457063 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨2, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (10500196483687 / 12500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214186457063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_3 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20991683024237 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214190480137 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨3, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20991683024237 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214190480137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_4 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83931917065559 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553548614801 / 25000000000000 : ℝ))
      (E := (cell13016 ⟨4, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83931917065559 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553548614801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_5 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20974281684869 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442839692003 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨5, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20974281684869 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442839692003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_6 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83862361083031 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214202490179 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨6, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83862361083031 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214202490179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_7 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (10478452507593 / 12500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (44284129981 / 2000000000000 : ℝ))
      (E := (cell13016 ⟨7, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (10478452507593 / 12500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (44284129981 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_8 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (2094822590933 / 2500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214210493661 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨8, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (2094822590933 / 2500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214210493661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_9 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83758211777649 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107107240397 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨9, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83758211777649 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107107240397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_10 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (16744708889361 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214218525059 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨10, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (16744708889361 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214218525059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_11 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83688901610041 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107111258307 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨11, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83688901610041 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107111258307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_12 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41827141616397 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107113259773 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨12, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41827141616397 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107113259773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_13 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83619689280679 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (17298676091 / 781250000000 : ℝ))
      (E := (cell13016 ⟨13, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83619689280679 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (17298676091 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_14 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83585119719489 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276779315537 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨14, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83585119719489 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276779315537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_15 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20887643628799 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (138389908557 / 6250000000000 : ℝ))
      (E := (cell13016 ⟨15, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20887643628799 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (138389908557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_16 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83516053633947 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214242524339 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨16, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83516053633947 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214242524339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_17 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (5217597315129 / 6250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107123274781 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨17, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (5217597315129 / 6250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107123274781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_18 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20861771176511 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553562639723 / 25000000000000 : ℝ))
      (E := (cell13016 ⟨18, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20861771176511 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553562639723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_19 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (16682527318511 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553563639149 / 25000000000000 : ℝ))
      (E := (cell13016 ⟨19, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (16682527318511 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553563639149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13017_0 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (1050891392261 / 1250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107032281219 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨0, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (1050891392261 / 1250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107032281219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_1 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (42018211012041 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214068577001 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨1, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (42018211012041 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214068577001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_2 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (84001557480717 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214072589041 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨2, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (84001557480717 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214072589041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_3 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (1679334354291 / 2000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276759575867 / 12500000000000 : ℝ))
      (E := (cell13017 ⟨3, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (1679334354291 / 2000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276759575867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_4 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41965951344769 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214080580869 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨4, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41965951344769 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214080580869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_5 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (3355884494793 / 4000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107042288297 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨5, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (3355884494793 / 4000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107042288297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_6 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (16772469343949 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (55352215043 / 2500000000000 : ℝ))
      (E := (cell13017 ⟨6, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (16772469343949 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (55352215043 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_7 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (10478450712977 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214092605599 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨7, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (10478450712977 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214092605599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_8 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41896444643373 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (34595259301 / 1562500000000 : ℝ))
      (E := (cell13017 ⟨8, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41896444643373 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (34595259301 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_9 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83758197433423 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44282012711 / 2000000000000 : ℝ))
      (E := (cell13017 ⟨9, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83758197433423 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44282012711 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_10 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83723530108921 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (138381538557 / 6250000000000 : ℝ))
      (E := (cell13017 ⟨10, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83723530108921 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (138381538557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_11 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83688887278493 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214108661761 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨11, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83688887278493 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214108661761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_12 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83654268907577 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214112659959 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨12, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83654268907577 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214112659959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_13 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83619674961787 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214116675373 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨13, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83619674961787 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214116675373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_14 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83585105406917 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (110706032769 / 5000000000000 : ℝ))
      (E := (cell13017 ⟨14, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83585105406917 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (110706032769 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_15 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83550560208939 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214124663401 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨15, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83550560208939 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214124663401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_16 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41758019666999 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (138383044031 / 6250000000000 : ℝ))
      (E := (cell13017 ⟨16, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41758019666999 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (138383044031 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_17 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83481542748419 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107066333501 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨17, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83481542748419 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107066333501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_18 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (10430883802337 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107068335939 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨18, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (10430883802337 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107068335939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_19 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (166825244623 / 200000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214140723459 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨19, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (166825244623 / 200000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214140723459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13018_0 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16814259396307 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213950700553 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨0, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16814259396307 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213950700553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_1 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (84036407631129 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213954709843 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨1, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (84036407631129 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213954709843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_2 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (84001543094151 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213958716657 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨2, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (84001543094151 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213958716657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_3 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16793340666873 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213962729373 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨3, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16793340666873 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213962729373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_4 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (5245743019733 / 6250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213966756109 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨4, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (5245743019733 / 6250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213966756109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_5 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (5243568625149 / 6250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213970746773 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨5, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (5243568625149 / 6250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213970746773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_6 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20965583089667 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213974766883 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨6, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20965583089667 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213974766883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_7 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41913795674549 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106989382897 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨7, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41913795674549 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106989382897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_8 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (4189643746919 / 5000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106991375269 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨8, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (4189643746919 / 5000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106991375269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_9 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83758183091403 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213986785951 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨9, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83758183091403 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213986785951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_10 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41861757886621 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442798152497 / 20000000000000 : ℝ))
      (E := (cell13018 ⟨10, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41861757886621 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442798152497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_11 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (1673777458983 / 2000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213994802553 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨11, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (1673777458983 / 2000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2213994802553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_12 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20913563646141 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106999398009 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨12, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20913563646141 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1106999398009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_13 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83619660645099 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276750350843 / 12500000000000 : ℝ))
      (E := (cell13018 ⟨13, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83619660645099 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276750350843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_14 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20896272774137 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214006782111 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨14, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20896272774137 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214006782111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_15 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41775272952441 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214010843731 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨15, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41775272952441 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214010843731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_16 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (66812820029 / 80000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214014822087 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨16, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (66812820029 / 80000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214014822087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_17 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20870382114243 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553504709583 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨17, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20870382114243 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553504709583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_18 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41723528066773 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214022838779 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨18, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41723528066773 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214022838779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_19 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83412608032641 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (221402682769 / 10000000000000 : ℝ))
      (E := (cell13018 ⟨19, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83412608032641 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (221402682769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13019_0 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (21017820646101 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213836892149 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨0, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (21017820646101 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213836892149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_1 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (8403639324039 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (221384089619 / 10000000000000 : ℝ))
      (E := (cell13019 ⟨1, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (8403639324039 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (221384089619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_2 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (42000764354899 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106922448901 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨2, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (42000764354899 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106922448901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_3 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (10495836119549 / 12500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213848905363 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨3, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (10495836119549 / 12500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213848905363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_4 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83931873944129 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213852926991 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨4, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83931873944129 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213852926991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_5 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41948541818577 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213856912593 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨5, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41948541818577 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213856912593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_6 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (419311589999 / 500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213860927691 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨6, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (419311589999 / 500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213860927691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_7 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83827576996587 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106932460817 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨7, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83827576996587 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106932460817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_8 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (4189643029611 / 5000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213868959487 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨8, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (4189643029611 / 5000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213868959487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_9 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (8375816875159 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106936465999 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨9, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (8375816875159 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106936465999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_10 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83723501439769 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213876961781 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨10, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83723501439769 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213876961781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_11 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20922214655503 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106940469497 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨11, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20922214655503 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106940469497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_12 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41827120131877 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (276735623231 / 12500000000000 : ℝ))
      (E := (cell13019 ⟨12, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41827120131877 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (276735623231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_13 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20904911582653 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (276736123989 / 12500000000000 : ℝ))
      (E := (cell13019 ⟨13, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20904911582653 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (276736123989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_14 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83585076788379 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213892962663 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨14, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83585076788379 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213892962663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_15 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41775265801513 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106948480761 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨15, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41775265801513 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106948480761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_16 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (835160107407 / 1000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213900993547 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨16, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (835160107407 / 1000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213900993547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_17 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20870378541931 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553476251329 / 25000000000000 : ℝ))
      (E := (cell13019 ⟨17, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20870378541931 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553476251329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_18 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41723520925297 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213909001333 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨18, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41723520925297 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213909001333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_19 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83412593755979 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553478261037 / 25000000000000 : ℝ))
      (E := (cell13019 ⟨19, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83412593755979 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553478261037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13020_0 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (5254454261843 / 6250000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276715384923 / 12500000000000 : ℝ))
      (E := (cell13020 ⟨0, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (5254454261843 / 6250000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276715384923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_1 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (16807275770373 / 20000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69178971193 / 3125000000000 : ℝ))
      (E := (cell13020 ⟨1, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (16807275770373 / 20000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69178971193 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_2 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (84001514327657 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553432768647 / 25000000000000 : ℝ))
      (E := (cell13020 ⟨2, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (84001514327657 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553432768647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_3 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (8396667458063 / 10000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442747015399 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨3, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (8396667458063 / 10000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442747015399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_4 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (4196592978737 / 5000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213739093517 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨4, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (4196592978737 / 5000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213739093517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_5 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83897069274133 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213743132017 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨5, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83897069274133 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213743132017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_6 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83862303643141 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553436785531 / 25000000000000 : ℝ))
      (E := (cell13020 ⟨6, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83862303643141 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553436785531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_7 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20956890661571 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (17710009049 / 800000000000 : ℝ))
      (E := (cell13020 ⟨7, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20956890661571 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (17710009049 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_8 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83792846248267 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106877553027 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨8, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83792846248267 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106877553027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_9 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41879077206991 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69179972867 / 3125000000000 : ℝ))
      (E := (cell13020 ⟨9, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41879077206991 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69179972867 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_10 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (167446974217 / 200000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (88550526269 / 4000000000000 : ℝ))
      (E := (cell13020 ⟨10, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (167446974217 / 200000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (88550526269 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_11 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20922211074269 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69180222787 / 3125000000000 : ℝ))
      (E := (cell13020 ⟨11, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20922211074269 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (69180222787 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_12 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83654225945147 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (4323771819 / 195312500000 : ℝ))
      (E := (cell13020 ⟨12, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83654225945147 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (4323771819 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_13 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83619632018327 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213775172731 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨13, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83619632018327 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213775172731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_14 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83585062482411 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442755839407 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨14, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83585062482411 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442755839407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_15 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83550517303369 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213783191349 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨15, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83550517303369 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213783191349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_16 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83515996447349 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213787160661 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨16, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83515996447349 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213787160661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_17 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83481499880673 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442758233591 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨17, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83481499880673 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442758233591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_18 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41723513784919 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106897608903 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨18, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41723513784919 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106897608903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_19 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83412579481513 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276724899747 / 12500000000000 : ℝ))
      (E := (cell13020 ⟨19, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83412579481513 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276724899747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13021_0 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (42035626898393 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (22136093201 / 1000000000000 : ℝ))
      (E := (cell13021 ⟨0, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (42035626898393 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (22136093201 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_1 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (5252272779097 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213613313669 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨1, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (5252272779097 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213613313669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_2 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (5250093746733 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276702163113 / 12500000000000 : ℝ))
      (E := (cell13021 ⟨2, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (5250093746733 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276702163113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_3 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83966660207079 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213621302181 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨3, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83966660207079 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213621302181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_4 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41965922603781 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213625313619 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨4, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41965922603781 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213625313619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_5 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83897054913321 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553407336771 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨5, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83897054913321 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553407336771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_6 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83862289288689 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553408338051 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨6, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83862289288689 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553408338051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_7 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83827548298187 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213637336263 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨7, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83827548298187 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213637336263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_8 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83792831906521 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553410341081 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨8, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83792831906521 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553410341081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_9 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83758140078579 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213645327139 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨9, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83758140078579 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213645327139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_10 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (16744694555887 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213649347319 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨10, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (16744694555887 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213649347319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_11 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10461103746793 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213653373121 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨11, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10461103746793 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213653373121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_12 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41827105814371 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213657352459 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨12, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41827105814371 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213657352459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_13 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83619617708243 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213661407347 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨13, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83619617708243 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213661407347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_14 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83585048178643 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213665368891 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨14, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83585048178643 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213665368891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_15 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83550503005911 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (221366941683 / 10000000000000 : ℝ))
      (E := (cell13021 ⟨15, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83550503005911 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (221366941683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_16 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20878995539049 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442734676329 / 20000000000000 : ℝ))
      (E := (cell13021 ⟨16, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20878995539049 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442734676329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_17 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (4174074279791 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276709673061 / 12500000000000 : ℝ))
      (E := (cell13021 ⟨17, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (4174074279791 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276709673061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_18 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83447013291279 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106840714967 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨18, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83447013291279 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106840714967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_19 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41706282604621 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213685405747 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨19, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41706282604621 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213685405747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13022_0 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (84071239406297 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213495556457 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨0, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (84071239406297 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213495556457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_1 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (21009087520363 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106749772401 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨1, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (21009087520363 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106749772401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_2 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (8400148557001 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106751765431 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨2, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (8400148557001 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106751765431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_3 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83966645835739 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213507523009 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨3, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83966645835739 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213507523009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_4 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (2622869713831 / 3125000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213511529367 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨4, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (2622869713831 / 3125000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213511529367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_5 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83897040554717 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213515557797 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨5, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83897040554717 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213515557797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_6 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (16772454987289 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213519557929 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨6, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (16772454987289 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213519557929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_7 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41913766976149 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553380898763 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨7, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41913766976149 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553380898763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_8 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83792817566979 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442705512043 / 20000000000000 : ℝ))
      (E := (cell13022 ⟨8, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83792817566979 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442705512043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_9 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (4187906287269 / 5000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106765788117 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨9, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (4187906287269 / 5000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106765788117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_10 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41861729226287 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553383897909 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨10, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41861729226287 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553383897909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_11 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41844407826907 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213539612709 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨11, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41844407826907 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213539612709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_12 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41827098657269 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553385896841 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨12, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41827098657269 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553385896841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_13 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (2090490085009 / 2500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442709527523 / 20000000000000 : ℝ))
      (E := (cell13022 ⟨13, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (2090490085009 / 2500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442709527523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_14 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (3343401355083 / 4000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106775826369 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨14, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (3343401355083 / 4000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106775826369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_15 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83550488710653 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442711127593 / 20000000000000 : ℝ))
      (E := (cell13022 ⟨15, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83550488710653 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442711127593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_16 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83515967867241 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213559656499 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨16, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83515967867241 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213559656499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_17 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83481471313163 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553390913729 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨17, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83481471313163 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553390913729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_18 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (16689399802983 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (55339190943 / 2500000000000 : ℝ))
      (E := (cell13022 ⟨18, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (16689399802983 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (55339190943 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_19 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41706275469583 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106785833731 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨19, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41706275469583 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106785833731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13023_0 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (84071225018021 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213381788457 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨0, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (84071225018021 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213381788457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_1 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (84036335699563 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213385771581 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨1, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (84036335699563 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213385771581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_2 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (10500183899313 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213389810353 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨2, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (10500183899313 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213389810353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_3 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (5247914466663 / 6250000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553348449349 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨3, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (5247914466663 / 6250000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553348449349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_4 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (10491477059979 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276674724837 / 12500000000000 : ℝ))
      (E := (cell13023 ⟨4, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (10491477059979 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276674724837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_5 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83897026198321 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553350455529 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨5, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83897026198321 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553350455529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_6 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (10482782573301 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553351454321 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨6, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (10482782573301 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553351454321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_7 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41913759804307 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (221340984949 / 10000000000000 : ℝ))
      (E := (cell13023 ⟨7, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41913759804307 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (221340984949 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_8 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83792803229643 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553353466953 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨8, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83792803229643 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553353466953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_9 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41879055707193 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213417879031 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨9, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41879055707193 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213417879031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_10 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16744688825583 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213421831607 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨10, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16744688825583 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213421831607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_11 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83688801335487 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213425847949 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨11, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83688801335487 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213425847949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_12 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16730836600507 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442685975209 / 20000000000000 : ℝ))
      (E := (cell13023 ⟨12, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16730836600507 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442685975209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_13 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83619589094677 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213433863537 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨13, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83619589094677 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213433863537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_14 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16717003915541 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276679734259 / 12500000000000 : ℝ))
      (E := (cell13023 ⟨14, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16717003915541 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276679734259 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_15 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (10443809302199 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213441912949 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨15, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (10443809302199 / 12500000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213441912949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_16 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83515953580483 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213445927011 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨16, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83515953580483 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213445927011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_17 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83481457032703 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213449921001 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨17, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83481457032703 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213449921001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_18 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83446984740747 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213453899427 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨18, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83446984740747 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213453899427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_19 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (20853134167821 / 25000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213457924837 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨19, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (20853134167821 / 25000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213457924837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13024_0 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (42035605315979 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (110663403697 / 5000000000000 : ℝ))
      (E := (cell13024 ⟨0, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (42035605315979 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (110663403697 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_1 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (42018160659943 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553318027433 / 25000000000000 : ℝ))
      (E := (cell13024 ⟨1, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (42018160659943 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553318027433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_2 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (84001456821207 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213276085489 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨2, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (84001456821207 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213276085489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_3 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83966617099687 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553320016857 / 25000000000000 : ℝ))
      (E := (cell13024 ⟨3, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83966617099687 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553320016857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_4 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (1049147526491 / 1250000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213284121607 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨4, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (1049147526491 / 1250000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213284121607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_5 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (20974252961033 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213288082083 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨5, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (20974252961033 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213288082083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_6 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41931123119289 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213292130269 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨6, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41931123119289 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213292130269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_7 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16765501053427 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213296099579 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨7, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16765501053427 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213296099579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_8 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83792788894511 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213300113031 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨8, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83792788894511 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213300113031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_9 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16751619417119 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553326029857 / 25000000000000 : ℝ))
      (E := (cell13024 ⟨9, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16751619417119 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553326029857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_10 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (4186171490273 / 5000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213308125303 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨10, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (4186171490273 / 5000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213308125303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_11 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83688787019361 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213312136941 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨11, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83688787019361 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213312136941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_12 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83654168692733 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213316160379 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨12, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83654168692733 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213316160379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_13 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41809787395597 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (110666007163 / 5000000000000 : ℝ))
      (E := (cell13024 ⟨13, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41809787395597 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (110666007163 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_14 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16717001056107 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221332414923 / 10000000000000 : ℝ))
      (E := (cell13024 ⟨14, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16717001056107 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221332414923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_15 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83550460126729 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213328183589 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨15, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83550460126729 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213328183589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_16 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41757969647961 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213332193179 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨16, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41757969647961 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213332193179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_17 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41740721377219 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106668091373 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨17, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41740721377219 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106668091373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_18 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83446970468773 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442668043011 / 20000000000000 : ℝ))
      (E := (cell13024 ⟨18, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83446970468773 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442668043011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_19 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (20853130601399 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213344236157 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨19, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (20853130601399 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213344236157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

end BstLean.Part268
