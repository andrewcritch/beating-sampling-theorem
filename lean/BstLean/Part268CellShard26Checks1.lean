import BstLean.Part268CellShard26Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13000_20 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (10422305170473 / 12500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216083727617 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨20, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (10422305170473 / 12500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216083727617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_21 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83344041495417 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216087726109 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨21, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83344041495417 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216087726109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_22 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41654832875351 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (22160917819 / 1000000000000 : ℝ))
      (E := (cell13000 ⟨22, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41654832875351 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (22160917819 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_23 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20818828524247 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110804789081 / 5000000000000 : ℝ))
      (E := (cell13000 ⟨23, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20818828524247 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (110804789081 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_24 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83240986501793 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216099786679 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨24, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83240986501793 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216099786679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_25 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83206682932799 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554025949981 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨25, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83206682932799 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554025949981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_26 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (16634480671571 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216107765521 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨26, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (16634480671571 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216107765521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_27 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (3325525909799 / 4000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216111802721 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨27, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (3325525909799 / 4000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216111802721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_28 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (16620783212467 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108057898379 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨28, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (16620783212467 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108057898379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_29 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41534854139137 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216119807997 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨29, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41534854139137 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216119807997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_30 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83035524361293 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216123838131 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨30, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83035524361293 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216123838131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_31 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (83001364280051 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216127830057 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨31, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (83001364280051 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216127830057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_32 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (8296722800337 / 10000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216131843529 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨32, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (8296722800337 / 10000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216131843529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_33 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82933115500227 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (138508488809 / 6250000000000 : ℝ))
      (E := (cell13000 ⟨33, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82933115500227 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (138508488809 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_34 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82899026739759 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443227976057 / 20000000000000 : ℝ))
      (E := (cell13000 ⟨34, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82899026739759 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443227976057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_35 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82864961691259 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216143846207 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨35, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82864961691259 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216143846207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_36 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82830920324173 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (44322957899 / 2000000000000 : ℝ))
      (E := (cell13000 ⟨36, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82830920324173 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (44322957899 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_37 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (16559380521621 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277018988661 / 12500000000000 : ℝ))
      (E := (cell13000 ⟨37, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (16559380521621 / 20000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277018988661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_38 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20690727128203 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216155889039 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨38, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20690727128203 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216155889039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_39 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41364469004101 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216159892557 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨39, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41364469004101 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216159892557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13001_20 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83378427053813 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (69249046667 / 3125000000000 : ℝ))
      (E := (cell13001 ⟨20, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83378427053813 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (69249046667 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_21 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83344027191743 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (138498342959 / 6250000000000 : ℝ))
      (E := (cell13001 ⟨21, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83344027191743 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (138498342959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_22 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83309651453319 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443195496067 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨22, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83309651453319 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443195496067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_23 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20818824951473 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (276997691751 / 12500000000000 : ℝ))
      (E := (cell13001 ⟨23, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20818824951473 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (276997691751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_24 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83240972216977 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107992767357 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨24, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83240972216977 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1107992767357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_25 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41603334327129 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215989543653 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨25, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41603334327129 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2215989543653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_26 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (16634477817117 / 20000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553998390859 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨26, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (16634477817117 / 20000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (553998390859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_27 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (8313813347897 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (88639901519 / 4000000000000 : ℝ))
      (E := (cell13001 ⟨27, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (8313813347897 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (88639901519 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_28 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (83103901802589 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443200305569 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨28, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (83103901802589 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443200305569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_29 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41534847012391 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216005534963 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨29, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41534847012391 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216005534963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_30 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (1660710202281 / 2000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108004780511 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨30, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (1660710202281 / 2000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108004780511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_31 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20750337509763 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554003401871 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨31, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20750337509763 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554003401871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_32 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82967213768609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216017616997 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨32, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82967213768609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216017616997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_33 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82933101271699 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (4432043181 / 200000000000 : ℝ))
      (E := (cell13001 ⟨33, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82933101271699 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (4432043181 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_34 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82899012517459 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (110801279367 / 5000000000000 : ℝ))
      (E := (cell13001 ⟨34, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82899012517459 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (110801279367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_35 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82864947475181 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216029608077 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨35, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82864947475181 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216029608077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_36 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82830906114313 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216033653047 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨36, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82830906114313 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216033653047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_37 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41398444202229 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (277004707957 / 12500000000000 : ℝ))
      (E := (cell13001 ⟨37, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41398444202229 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (277004707957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_38 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20690723578843 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108020819863 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨38, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20690723578843 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108020819863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_39 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20682230954241 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216045639609 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨39, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20682230954241 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216045639609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13002_20 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41689206373023 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553963813677 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨20, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41689206373023 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553963813677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_21 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (2604500402821 / 3125000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107929651273 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨21, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (2604500402821 / 3125000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107929651273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_22 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83309637158139 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443172658223 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨22, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83309637158139 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443172658223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_23 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20818821379249 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215867282037 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨23, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20818821379249 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215867282037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_24 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83240957934361 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221587127839 / 10000000000000 : ℝ))
      (E := (cell13002 ⟨24, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83240957934361 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221587127839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_25 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83206654377917 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215875283023 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨25, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83206654377917 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215875283023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_26 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83172374815513 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215879298547 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨26, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83172374815513 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215879298547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_27 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83138119215161 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138492707959 / 6250000000000 : ℝ))
      (E := (cell13002 ⟨27, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83138119215161 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138492707959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_28 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83103887545039 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221588731307 / 10000000000000 : ℝ))
      (E := (cell13002 ⟨28, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83103887545039 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221588731307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_29 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41534839886743 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215891316091 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨29, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41534839886743 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215891316091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_30 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (83035495869001 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (22158953381 / 1000000000000 : ℝ))
      (E := (cell13002 ⟨30, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (83035495869001 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (22158953381 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_31 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41500667900123 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215899380557 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨31, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41500667900123 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215899380557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_32 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (2074179988401 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215903386113 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨32, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (2074179988401 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215903386113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_33 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82933087045363 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215907355703 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨33, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82933087045363 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215907355703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_34 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (1657979965947 / 2000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215911407313 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨34, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (1657979965947 / 2000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215911407313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_35 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82864933261293 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215915365597 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨35, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82864933261293 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215915365597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_36 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41415445953321 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215919406793 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨36, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41415445953321 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215919406793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_37 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41398437101499 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553980853419 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨37, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41398437101499 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553980853419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_38 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82762880120119 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107963722397 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨38, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82762880120119 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107963722397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_39 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (10341113703489 / 12500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107965720533 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨39, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (10341113703489 / 12500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107965720533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13003_20 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41689199220241 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110787053501 / 5000000000000 : ℝ))
      (E := (cell13003 ⟨20, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41689199220241 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110787053501 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_21 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83343998591003 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110787252753 / 5000000000000 : ℝ))
      (E := (cell13003 ⟨21, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83343998591003 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110787252753 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_22 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (2082740571629 / 2500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215749097537 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨22, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (2082740571629 / 2500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215749097537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_23 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83275271230301 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443150616817 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨23, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83275271230301 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443150616817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_24 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16648188730789 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215757076111 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨24, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16648188730789 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215757076111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_25 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (3328265604151 / 4000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443152226977 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨25, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (3328265604151 / 4000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443152226977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_26 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41586180273819 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215765087751 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨26, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41586180273819 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215765087751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_27 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (83138104953549 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215769112359 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨27, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (83138104953549 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215769112359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_28 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16620774657937 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215773152437 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨28, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16620774657937 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215773152437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_29 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (2595927047637 / 3125000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443155430277 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨29, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (2595927047637 / 3125000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443155430277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_30 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41517740813073 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276972646171 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨30, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41517740813073 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276972646171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_31 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (5187582597727 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107892574641 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨31, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (5187582597727 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107892574641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_32 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82967185305663 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (13848682193 / 625000000000 : ℝ))
      (E := (cell13003 ⟨32, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82967185305663 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (13848682193 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_33 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82933072821217 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215793175171 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨33, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82933072821217 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215793175171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_34 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (8289898407943 / 10000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443159432861 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨34, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (8289898407943 / 10000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443159432861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_35 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16572983809919 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215801177427 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨35, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16572983809919 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215801177427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_36 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82830877701159 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553951303719 / 25000000000000 : ℝ))
      (E := (cell13003 ⟨36, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82830877701159 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553951303719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_37 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41398430001863 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276976152257 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨37, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41398430001863 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276976152257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_38 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82762865927051 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215813245519 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨38, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82762865927051 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215813245519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_39 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16545779088209 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110790861909 / 5000000000000 : ℝ))
      (E := (cell13003 ⟨39, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16545779088209 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (110790861909 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13004_20 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83378384137121 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221562688097 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨20, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83378384137121 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221562688097 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_21 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (5208999018371 / 6250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107815459937 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨21, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (5208999018371 / 6250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107815459937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_22 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41654804287191 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215634899601 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨22, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41654804287191 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215634899601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_23 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83275256945807 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215638940151 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨23, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83275256945807 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215638940151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_24 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (5202558085983 / 6250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107821463937 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨24, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (5202558085983 / 6250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107821463937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_25 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (8320662583183 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (34619483187 / 1562500000000 : ℝ))
      (E := (cell13004 ⟨25, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (8320662583183 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (34619483187 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_26 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83172346281961 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107825465523 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨26, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83172346281961 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107825465523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_27 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41569045347067 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221565495149 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨27, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41569045347067 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221565495149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_28 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41551929518263 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443131785791 / 20000000000000 : ℝ))
      (E := (cell13004 ⟨28, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41551929518263 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443131785791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_29 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (20767412819369 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215662982327 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨29, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (20767412819369 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215662982327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_30 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (20758866846371 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553916749071 / 25000000000000 : ℝ))
      (E := (cell13004 ⟨30, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (20758866846371 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553916749071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_31 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (83001307329211 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215670972219 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨31, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (83001307329211 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215670972219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_32 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41483585538739 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215674969883 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨32, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41483585538739 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215674969883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_33 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41466529299631 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215678990289 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨33, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41466529299631 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215678990289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_34 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (828989698637 / 1000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215683034217 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨34, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (828989698637 / 1000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215683034217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_35 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (20716226210021 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221568704357 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨35, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (20716226210021 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221568704357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_36 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82830863497863 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553922754653 / 25000000000000 : ℝ))
      (E := (cell13004 ⟨36, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82830863497863 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553922754653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_37 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (1034960572583 / 1250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221569501809 / 10000000000000 : ℝ))
      (E := (cell13004 ⟨37, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (1034960572583 / 1250000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (221569501809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_38 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (8276285173617 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215699041897 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨38, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (8276285173617 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215699041897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_39 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82728881256363 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44314060619 / 2000000000000 : ℝ))
      (E := (cell13004 ⟨39, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82728881256363 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44314060619 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13005_20 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83378369835963 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221551274587 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨20, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83378369835963 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221551274587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_21 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83343969999071 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215516722001 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨21, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83343969999071 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215516722001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_22 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (20827398571451 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215520755663 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨22, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (20827398571451 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215520755663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_23 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83275242663511 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443104958373 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨23, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83275242663511 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443104958373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_24 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (8324091509971 / 10000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553882193821 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨24, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (8324091509971 / 10000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553882193821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_25 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (83206611562083 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215532767121 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨25, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (83206611562083 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215532767121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_26 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (1039654150231 / 1250000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221553676999 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨26, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (1039654150231 / 1250000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221553676999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_27 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41569038218457 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221554078627 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨27, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41569038218457 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221554078627 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_28 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41551922392781 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (34617887783 / 1562500000000 : ℝ))
      (E := (cell13005 ⟨28, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41551922392781 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (34617887783 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_29 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41534818516381 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215548808919 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨29, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41534818516381 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215548808919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_30 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16607090629403 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553888204713 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨30, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16607090629403 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553888204713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_31 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41500646548491 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215556849373 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨31, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41500646548491 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215556849373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_32 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82967156851483 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215560843129 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨32, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82967156851483 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215560843129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_33 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (10366630547437 / 12500000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215564859673 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨33, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (10366630547437 / 12500000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215564859673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_34 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82898955650159 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (44311376823 / 2000000000000 : ℝ))
      (E := (cell13005 ⟨34, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82898955650159 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (44311376823 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_35 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41432445316381 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221557284671 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨35, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41432445316381 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221557284671 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_36 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16566169859351 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107788438343 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨36, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16566169859351 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107788438343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_37 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (4139841580587 / 5000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276947609061 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨37, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (4139841580587 / 5000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276947609061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_38 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82762837547473 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276948111583 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨38, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82762837547473 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276948111583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_39 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16545773414773 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215588878131 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨39, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16545773414773 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215588878131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13006_20 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83378355537007 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215398606411 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨20, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83378355537007 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215398606411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_21 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83343955706407 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215402636431 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨21, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83343955706407 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215402636431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_22 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83309579999427 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215406607367 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨22, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83309579999427 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215406607367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_23 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (16655045676683 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215410639221 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨23, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (16655045676683 / 20000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215410639221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_24 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (8324090082589 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215414618337 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨24, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (8324090082589 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215414618337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_25 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41603298647267 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276927333043 / 12500000000000 : ℝ))
      (E := (cell13006 ⟨25, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41603298647267 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276927333043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_26 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (20793079439299 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215422663027 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨26, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (20793079439299 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215422663027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_27 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (8313806218189 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (69232083599 / 3125000000000 : ℝ))
      (E := (cell13006 ⟨27, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (8313806218189 / 10000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (69232083599 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_28 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (10387978817099 / 12500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215430644423 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨28, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (10387978817099 / 12500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215430644423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_29 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (83069622790241 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107717344839 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨29, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (83069622790241 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107717344839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_30 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41517719455369 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215438695611 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨30, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41517719455369 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215438695611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_31 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (162111872787 / 195312500000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107721361089 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨31, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (162111872787 / 195312500000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107721361089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_32 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82967142627679 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215446712027 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨32, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82967142627679 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215446712027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_33 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (32395714907 / 39062500000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215450724709 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨33, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (32395714907 / 39062500000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215450724709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_34 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41449470719403 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215454702371 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨34, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41449470719403 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215454702371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_35 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82864876427627 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215458762821 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨35, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82864876427627 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215458762821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_36 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82830835097833 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138466420651 / 6250000000000 : ℝ))
      (E := (cell13006 ⟨36, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82830835097833 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138466420651 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_37 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (3311872696761 / 4000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (34616668457 / 1562500000000 : ℝ))
      (E := (cell13006 ⟨37, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (3311872696761 / 4000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (34616668457 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_38 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82762823360961 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138466921193 / 6250000000000 : ℝ))
      (E := (cell13006 ⟨38, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82762823360961 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138466921193 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_39 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (1654577057871 / 2000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553868694931 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨39, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (1654577057871 / 2000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553868694931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13007_20 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (20844585310063 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (276910565113 / 12500000000000 : ℝ))
      (E := (cell13007 ⟨20, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (20844585310063 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (276910565113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_21 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83343941415943 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138455530511 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨21, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83343941415943 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138455530511 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_22 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83309565715249 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138455782067 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨22, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83309565715249 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138455782067 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_23 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83275214105517 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107648270301 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨23, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83275214105517 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107648270301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_24 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83240886554267 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215300515441 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨24, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83240886554267 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215300515441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_25 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (4160329151459 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215304557217 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨25, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (4160329151459 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215304557217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_26 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83172303498107 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107654275857 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨26, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83172303498107 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107654275857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_27 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (4156902396453 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215312559717 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨27, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (4156902396453 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215312559717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_28 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (16620763258043 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138457286461 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨28, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (16620763258043 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138457286461 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_29 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83069608549913 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (221532056609 / 10000000000000 : ℝ))
      (E := (cell13007 ⟨29, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83069608549913 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (221532056609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_30 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41517712338327 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107662284011 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨30, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41517712338327 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107662284011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_31 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (83001264639097 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215328590637 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨31, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (83001264639097 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215328590637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_32 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (5185445525379 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110766628829 / 5000000000000 : ℝ))
      (E := (cell13007 ⟨32, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (5185445525379 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110766628829 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_33 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82933015946533 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107668292701 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨33, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82933015946533 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107668292701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_34 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82898927229641 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443068123577 / 20000000000000 : ℝ))
      (E := (cell13007 ⟨34, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82898927229641 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443068123577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_35 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82864862224679 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553836153983 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨35, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82864862224679 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553836153983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_36 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82830820901097 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215348638487 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨36, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82830820901097 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215348638487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_37 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (5174800201781 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215352626961 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨37, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (5174800201781 / 6250000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215352626961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_38 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41381404588317 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215356639901 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨38, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41381404588317 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215356639901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_39 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82728838715419 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215360676977 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨39, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82728838715419 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215360676977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13008_20 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41689163472849 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (6922407597 / 312500000000 : ℝ))
      (E := (cell13008 ⟨20, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41689163472849 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (6922407597 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_21 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (130224886137 / 156250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215174452227 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨21, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (130224886137 / 156250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215174452227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_22 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (8330955143327 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215178414423 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨22, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (8330955143327 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215178414423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_23 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41637599914909 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215182437629 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨23, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41637599914909 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215182437629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_24 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83240872284841 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215186466593 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨24, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83240872284841 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215186466593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_25 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83206568766023 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215190445737 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨25, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83206568766023 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215190445737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_26 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (83172289241213 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215194494499 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨26, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (83172289241213 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215194494499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_27 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (10392254209803 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (553799624597 / 25000000000000 : ℝ))
      (E := (cell13008 ⟨27, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (10392254209803 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (553799624597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_28 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (10387975255729 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215202459483 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨28, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (10387975255729 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215202459483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_29 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41534797155889 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221520649667 / 10000000000000 : ℝ))
      (E := (cell13008 ⟨29, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41534797155889 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221520649667 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_30 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (2075885261119 / 2500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215210494629 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨30, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (2075885261119 / 2500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215210494629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_31 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (129689453771 / 156250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443042902663 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨31, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (129689453771 / 156250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443042902663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_32 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82967114186639 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (17721747963 / 800000000000 : ℝ))
      (E := (cell13008 ⟨32, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82967114186639 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (17721747963 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_33 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16586600346667 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (55380562509 / 2500000000000 : ℝ))
      (E := (cell13008 ⟨33, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16586600346667 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (55380562509 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_34 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (10362364127833 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107613264527 / 50000000000000 : ℝ))
      (E := (cell13008 ⟨34, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (10362364127833 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107613264527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_35 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41432424011959 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215230523357 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨35, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41432424011959 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215230523357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_36 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41415403353273 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215234542217 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨36, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41415403353273 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215234542217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_37 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82796789040151 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443047717149 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨37, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82796789040151 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443047717149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_38 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (8276279499449 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107621297551 / 50000000000000 : ℝ))
      (E := (cell13008 ⟨38, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (8276279499449 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107621297551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_39 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (8272882453947 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215246569891 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨39, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (8272882453947 / 10000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215246569891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13009_20 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (2605572270417 / 3125000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215056336823 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨20, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (2605572270417 / 3125000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215056336823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_21 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16668782568323 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107530176797 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨21, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16668782568323 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107530176797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_22 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (83309537153489 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (138441523111 / 6250000000000 : ℝ))
      (E := (cell13009 ⟨22, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (83309537153489 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (138441523111 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_23 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (20818796389079 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107534194341 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨23, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (20818796389079 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107534194341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_24 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (20810214504403 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107536206697 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨24, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (20810214504403 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107536206697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_25 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41603277252531 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553769097083 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨25, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41603277252531 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553769097083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_26 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41586137493257 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107540216467 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨26, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41586137493257 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107540216467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_27 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41569009714991 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (221508443271 / 10000000000000 : ℝ))
      (E := (cell13009 ⟨27, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41569009714991 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (221508443271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_28 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41551893901821 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215088448233 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨28, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41551893901821 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215088448233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_29 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41534790037917 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107546211453 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨29, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41534790037917 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107546211453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_30 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (83035396215057 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (221509641689 / 10000000000000 : ℝ))
      (E := (cell13009 ⟨30, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (83035396215057 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (221509641689 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_31 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41500618094987 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (69221888489 / 3125000000000 : ℝ))
      (E := (cell13009 ⟨31, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41500618094987 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (69221888489 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_32 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82967099969403 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (34611007319 / 1562500000000 : ℝ))
      (E := (cell13009 ⟨32, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82967099969403 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (34611007319 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_33 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (20733246880581 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215108469589 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨33, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (20733246880581 / 25000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215108469589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_34 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82898898817873 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107556247259 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨34, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82898898817873 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107556247259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_35 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82864833825343 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215116485101 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨35, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82864833825343 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215116485101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_36 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82830792514181 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215120500287 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨36, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82830792514181 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215120500287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_37 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82796774853991 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107562240741 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨37, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82796774853991 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107562240741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_38 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82762780814529 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553782121809 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨38, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82762780814529 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553782121809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_39 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10341101295713 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (110756625861 / 5000000000000 : ℝ))
      (E := (cell13009 ⟨39, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10341101295713 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (110756625861 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13010_20 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83378298363191 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (27686778707 / 1250000000000 : ℝ))
      (E := (cell13010 ⟨20, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83378298363191 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (27686778707 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_21 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (333375594231 / 400000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110747315447 / 5000000000000 : ℝ))
      (E := (cell13010 ⟨21, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (333375594231 / 400000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110747315447 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_22 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41654761437953 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107475160389 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨22, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41654761437953 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107475160389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_23 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83275171285011 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107477167693 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨23, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83275171285011 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107477167693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_24 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83240843752579 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107479177923 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨24, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83240843752579 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107479177923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_25 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (10400817530787 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214962385003 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨25, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (10400817530787 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214962385003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_26 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83172260734009 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214966367023 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨26, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83172260734009 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214966367023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_27 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83138005183733 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107485181343 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨27, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83138005183733 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107485181343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_28 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (20775943390911 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214974374143 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨28, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (20775943390911 / 25000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214974374143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_29 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (83069565842081 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (442995680663 / 20000000000000 : ℝ))
      (E := (cell13010 ⟨29, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (83069565842081 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (442995680663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_30 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16607076397509 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214982393349 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨30, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16607076397509 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214982393349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_31 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (10375152746087 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553746601051 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨31, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (10375152746087 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553746601051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_32 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16593417150871 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107495218557 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨32, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16593417150871 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107495218557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_33 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82932973313501 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214994434477 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨33, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82932973313501 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214994434477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_34 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82898884615269 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214998455641 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨34, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82898884615269 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2214998455641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_35 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82864819628953 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107501221253 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨35, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82864819628953 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107501221253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_36 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (20707694581 / 25000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110750322701 / 5000000000000 : ℝ))
      (E := (cell13010 ⟨36, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (20707694581 / 25000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110750322701 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_37 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82796760670013 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (276876311287 / 12500000000000 : ℝ))
      (E := (cell13010 ⟨37, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82796760670013 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (276876311287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_38 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (331051066547 / 400000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215014492493 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨38, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (331051066547 / 400000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215014492493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_39 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82728796194119 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215018460213 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨39, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82728796194119 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215018460213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13011_20 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83378284075237 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214828310251 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨20, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83378284075237 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214828310251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_21 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83343884276083 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442966463653 / 20000000000000 : ℝ))
      (E := (cell13011 ⟨21, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83343884276083 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442966463653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_22 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83309508600521 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107418162891 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨22, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83309508600521 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107418162891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_23 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41637578507951 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214840336117 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨23, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41637578507951 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214840336117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_24 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83240829489741 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (44296887047 / 2000000000000 : ℝ))
      (E := (cell13011 ⟨24, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83240829489741 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (44296887047 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_25 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (20801631497431 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214848318901 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨25, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (20801631497431 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214848318901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_26 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41586123241849 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221485235521 / 10000000000000 : ℝ))
      (E := (cell13011 ⟨26, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41586123241849 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221485235521 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_27 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83137990939677 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107428173393 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨27, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83137990939677 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107428173393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_28 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83103759325837 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107430177101 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨28, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83103759325837 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107430177101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_29 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83069551610519 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107432189689 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨29, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83069551610519 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107432189689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_30 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41517683881111 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214868365463 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨30, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41517683881111 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214868365463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_31 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (83001207749607 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (34607380819 / 1562500000000 : ℝ))
      (E := (cell13011 ⟨31, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (83001207749607 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (34607380819 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_32 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (16593414308299 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221487640147 / 10000000000000 : ℝ))
      (E := (cell13011 ⟨32, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (16593414308299 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221487640147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_33 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (5183309944179 / 6250000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214880395023 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨33, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (5183309944179 / 6250000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214880395023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_34 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82898870414851 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214884412423 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨34, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82898870414851 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214884412423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_35 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (20716201358687 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214888454229 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨35, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (20716201358687 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214888454229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_36 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82830764136003 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (138430778881 / 6250000000000 : ℝ))
      (E := (cell13011 ⟨36, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82830764136003 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (138430778881 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_37 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82796746488219 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (69215513627 / 3125000000000 : ℝ))
      (E := (cell13011 ⟨37, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82796746488219 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (69215513627 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_38 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41381376230577 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553725123353 / 25000000000000 : ℝ))
      (E := (cell13011 ⟨38, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41381376230577 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553725123353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_39 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (20682195506179 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107452228811 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨39, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (20682195506179 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107452228811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13012_20 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83378269789481 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214714319593 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨20, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83378269789481 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214714319593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_21 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41671934998307 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (55367958081 / 2500000000000 : ℝ))
      (E := (cell13012 ⟨21, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41671934998307 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (55367958081 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_22 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83309494327333 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107361163219 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨22, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83309494327333 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107361163219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_23 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83275142748989 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (885890533 / 40000000000 : ℝ))
      (E := (cell13012 ⟨23, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83275142748989 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (885890533 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_24 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83240815229099 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107365172253 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨24, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83240815229099 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107365172253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_25 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41603255867673 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214734365303 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨25, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41603255867673 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214734365303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_26 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83172232235579 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107369169527 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨26, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83172232235579 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107369169527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_27 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20784494174453 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107371192507 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨27, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20784494174453 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107371192507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_28 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41551872545111 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553686597103 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨28, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41551872545111 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553686597103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_29 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83069537381147 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107375204809 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨29, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83069537381147 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107375204809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_30 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (5189709596193 / 6250000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214754391779 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨30, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (5189709596193 / 6250000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214754391779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_31 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (83001193532707 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553689598713 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨31, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (83001193532707 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553689598713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_32 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41483528665411 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (88590496803 / 4000000000000 : ℝ))
      (E := (cell13012 ⟨32, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41483528665411 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (88590496803 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_33 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41466472451207 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107383204921 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨33, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41466472451207 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107383204921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_34 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41449428108309 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214770423503 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨34, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41449428108309 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214770423503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_35 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82864791242727 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (138423403851 / 6250000000000 : ℝ))
      (E := (cell13012 ⟨35, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82864791242727 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (138423403851 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_36 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (8283074995019 / 10000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442955693167 / 20000000000000 : ℝ))
      (E := (cell13012 ⟨36, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (8283074995019 / 10000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442955693167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_37 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (646849471161 / 781250000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553695623727 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨37, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (646849471161 / 781250000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553695623727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_38 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82762738287739 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553696622499 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨38, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82762738287739 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553696622499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_39 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82728767857493 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214790509451 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨39, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82728767857493 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214790509451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13013_20 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20844563876481 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276825040573 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨20, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20844563876481 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276825040573 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_21 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41671927859671 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107302191099 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨21, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41671927859671 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107302191099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_22 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41654740028171 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (22146083811 / 1000000000000 : ℝ))
      (E := (cell13013 ⟨22, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41654740028171 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (22146083811 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_23 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (5204695530267 / 6250000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107306191457 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨23, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (5204695530267 / 6250000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107306191457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_24 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83240800970651 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107308195359 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨24, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83240800970651 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107308195359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_25 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41603248741581 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214620407359 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨25, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41603248741581 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214620407359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_26 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41586108994827 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214624377 / 100000000000 : ℝ))
      (E := (cell13013 ⟨26, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41586108994827 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214624377 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_27 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (4156898122907 / 5000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107314209449 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨27, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (4156898122907 / 5000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107314209449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_28 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (83103730856797 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214632418281 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨28, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (83103730856797 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214632418281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_29 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (16613904630793 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553659108879 / 25000000000000 : ℝ))
      (E := (cell13013 ⟨29, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (16613904630793 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553659108879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_30 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (648713588423 / 781250000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276830051719 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨30, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (648713588423 / 781250000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276830051719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_31 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41500589658997 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214644412949 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨31, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41500589658997 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214644412949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_32 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82967043122337 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110732421717 / 5000000000000 : ℝ))
      (E := (cell13013 ⟨32, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82967043122337 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (110732421717 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_33 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (1658658614003 / 2000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442930495787 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨33, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (1658658614003 / 2000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442930495787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_34 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82898842020571 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (27683206111 / 1250000000000 : ℝ))
      (E := (cell13013 ⟨34, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82898842020571 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (27683206111 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_35 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82864777052891 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107330232333 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨35, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82864777052891 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107330232333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_36 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82830735766559 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214664465239 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨36, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82830735766559 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214664465239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_37 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82796718131179 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276833561339 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨37, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82796718131179 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276833561339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_38 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41381362058253 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107336241123 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨38, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41381362058253 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107336241123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_39 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (1654575073849 / 2000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107338249097 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨39, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (1654575073849 / 2000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107338249097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13014_20 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (16675648244913 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214486383533 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨20, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (16675648244913 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214486383533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_21 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (20835960361067 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107245218403 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨21, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (20835960361067 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107245218403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_22 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41654732893773 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442898886283 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨22, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41654732893773 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442898886283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_23 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (333100456887 / 400000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110724921449 / 5000000000000 : ℝ))
      (E := (cell13014 ⟨23, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (333100456887 / 400000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110724921449 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_24 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83240786714397 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276812804073 / 12500000000000 : ℝ))
      (E := (cell13014 ⟨24, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83240786714397 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276812804073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_25 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83206483233171 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214506445069 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨25, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83206483233171 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214506445069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_26 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (129956568353 / 156250000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553627617263 / 25000000000000 : ℝ))
      (E := (cell13014 ⟨26, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (129956568353 / 156250000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553627617263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_27 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41568974110329 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214514448439 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨27, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41568974110329 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214514448439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_28 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83103716625563 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442903688761 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨28, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83103716625563 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442903688761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_29 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (20767377232243 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214522457071 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨29, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (20767377232243 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214522457071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_30 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83035325099387 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276815811241 / 12500000000000 : ℝ))
      (E := (cell13014 ⟨30, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83035325099387 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276815811241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_31 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (83001165105469 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214530485271 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨31, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (83001165105469 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214530485271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_32 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82967028916037 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442906900571 / 20000000000000 : ℝ))
      (E := (cell13014 ⟨32, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82967028916037 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (442906900571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_33 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82932916500071 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221453854369 / 10000000000000 : ℝ))
      (E := (cell13014 ⟨33, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82932916500071 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221453854369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_34 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82898827826707 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214542549921 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨34, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82898827826707 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214542549921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_35 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41432381432619 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107273261019 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨35, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41432381432619 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107273261019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_36 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82830721585111 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221455051899 / 10000000000000 : ℝ))
      (E := (cell13014 ⟨36, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82830721585111 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221455051899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_37 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82796703955931 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214554540887 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨37, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82796703955931 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214554540887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_38 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82762709947453 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214558587621 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨38, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82762709947453 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214558587621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_39 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41364369764793 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221456260011 / 10000000000000 : ℝ))
      (E := (cell13014 ⟨39, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41364369764793 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221456260011 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13015_20 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20844556736351 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107186248221 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨20, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20844556736351 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107186248221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_21 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83343827171389 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553594121767 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨21, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83343827171389 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553594121767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_22 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41654725760473 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107190238691 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨22, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41654725760473 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107190238691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_23 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41637549980711 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55359613227 / 2500000000000 : ℝ))
      (E := (cell13015 ⟨23, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41637549980711 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55359613227 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_24 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (83240772460337 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442877705701 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨24, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (83240772460337 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442877705701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_25 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20801617246343 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107196268431 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨25, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20801617246343 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107196268431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_26 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41586094752189 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55359913919 / 2500000000000 : ℝ))
      (E := (cell13015 ⟨26, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41586094752189 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55359913919 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_27 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (10392241748171 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553600133027 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨27, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (10392241748171 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553600133027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_28 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41551851198259 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553601130871 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨28, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41551851198259 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553601130871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_29 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (10383686838271 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442881706561 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨29, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (10383686838271 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442881706561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_30 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41517655441409 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214412561763 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨30, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41517655441409 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214412561763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_31 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (8300115089513 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107208276627 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨31, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (8300115089513 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107208276627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_32 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20741753677981 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276802570879 / 12500000000000 : ℝ))
      (E := (cell13015 ⟨32, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20741753677981 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276802570879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_33 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82932902302177 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553606151027 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨33, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82932902302177 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553606151027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_34 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20724703408757 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (17715428853 / 800000000000 : ℝ))
      (E := (cell13015 ⟨34, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20724703408757 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (17715428853 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_35 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (10358093584971 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442886526747 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨35, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (10358093584971 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442886526747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_36 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16566141481169 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214436627089 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨36, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16566141481169 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214436627089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_37 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (5174793111429 / 6250000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442888129087 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨37, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (5174793111429 / 6250000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442888129087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_38 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (4138134789029 / 5000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442888925987 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨38, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (4138134789029 / 5000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442888925987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_39 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41364362684451 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214448638941 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨39, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41364362684451 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214448638941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13016_20 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83378212668439 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442851721001 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨20, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83378212668439 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442851721001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_21 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83343812900707 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442852518263 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨21, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83343812900707 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442852518263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_22 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (4165471862827 / 5000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214266577361 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨22, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (4165471862827 / 5000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214266577361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_23 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83275085703289 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442854124967 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨23, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83275085703289 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442854124967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_24 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83240758208469 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107137310043 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨24, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83240758208469 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107137310043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_25 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41603227369883 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214278624311 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨25, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41603227369883 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214278624311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_26 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83172175265027 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214282640127 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨26, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83172175265027 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214282640127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_27 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83137919752267 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214286669911 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨27, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83137919752267 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214286669911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_28 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41551844084831 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (55357266433 / 2500000000000 : ℝ))
      (E := (cell13016 ⟨28, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41551844084831 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (55357266433 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_29 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (5191842530347 / 6250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (6919670821 / 312500000000 : ℝ))
      (E := (cell13016 ⟨29, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (5191842530347 / 6250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (6919670821 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_30 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (83035296668437 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553574671951 / 25000000000000 : ℝ))
      (E := (cell13016 ⟨30, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (83035296668437 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553574671951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_31 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41500568343489 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214302675467 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨31, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41500568343489 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214302675467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_32 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (16593400101999 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276788335683 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨32, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (16593400101999 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276788335683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_33 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20733222026617 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214310718803 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨33, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20733222026617 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214310718803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_34 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20724699861383 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (34598667463 / 1562500000000 : ℝ))
      (E := (cell13016 ⟨34, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20724699861383 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (34598667463 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_35 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (517904590603 / 625000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (22143187411 / 1000000000000 : ℝ))
      (E := (cell13016 ⟨35, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (517904590603 / 625000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (22143187411 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_36 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82830693228761 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214322730857 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨36, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82830693228761 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214322730857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_37 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41398337805989 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553581686413 / 25000000000000 : ℝ))
      (E := (cell13016 ⟨37, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41398337805989 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (553581686413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_38 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41381340807943 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276791340831 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨38, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41381340807943 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276791340831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_39 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82728711210397 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442866946439 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨39, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82728711210397 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442866946439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13017_20 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83378198393671 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214144709221 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨20, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83378198393671 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214144709221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_21 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (4167189931611 / 5000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214148691217 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨21, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (4167189931611 / 5000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214148691217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_22 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83309422994329 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44283054627 / 2000000000000 : ℝ))
      (E := (cell13017 ⟨22, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83309422994329 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44283054627 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_23 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20818767861837 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276769589531 / 12500000000000 : ℝ))
      (E := (cell13017 ⟨23, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20818767861837 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276769589531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_24 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41620371979397 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (88566430629 / 4000000000000 : ℝ))
      (E := (cell13017 ⟨24, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41620371979397 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (88566430629 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_25 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83206440496351 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442832953169 / 20000000000000 : ℝ))
      (E := (cell13017 ⟨25, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83206440496351 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442832953169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_26 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83172161027867 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214168777601 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨26, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83172161027867 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214168777601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_27 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20784476380339 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214172744901 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨27, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20784476380339 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214172744901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_28 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (16620734788999 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (17298256147 / 781250000000 : ℝ))
      (E := (cell13017 ⟨28, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (16620734788999 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (17298256147 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_29 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20767366566781 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214180788297 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨29, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20767366566781 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214180788297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_30 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41517641228121 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214184809507 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨30, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41517641228121 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214184809507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_31 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (83001122481011 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (4324587487 / 195312500000 : ℝ))
      (E := (cell13017 ⟨31, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (83001122481011 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (4324587487 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_32 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20741746577563 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214192799559 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨32, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20741746577563 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214192799559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_33 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41466436956471 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442839365833 / 20000000000000 : ℝ))
      (E := (cell13017 ⟨33, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41466436956471 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442839365833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_34 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82898785258219 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442840164861 / 20000000000000 : ℝ))
      (E := (cell13017 ⟨34, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82898785258219 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442840164861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_35 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41432360157687 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214204844131 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨35, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41432360157687 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214204844131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_36 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41415339526929 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553552207573 / 25000000000000 : ℝ))
      (E := (cell13017 ⟨36, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41415339526929 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553552207573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_37 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82796661443271 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214212841539 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨37, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82796661443271 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214212841539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_38 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20690666863343 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214216877761 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨38, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20690666863343 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214216877761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_39 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (8272869705407 / 10000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107110439937 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨39, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (8272869705407 / 10000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107110439937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13018_20 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41689092060549 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214030867401 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨20, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41689092060549 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214030867401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_21 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (10417973045741 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107017422553 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨21, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (10417973045741 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107017422553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_22 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (10413676091789 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442807776199 / 20000000000000 : ℝ))
      (E := (cell13018 ⟨22, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (10413676091789 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442807776199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_23 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83275057193601 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (17297209857 / 781250000000 : ℝ))
      (E := (cell13018 ⟨23, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83275057193601 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (17297209857 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_24 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83240729711311 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107023453511 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨24, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83240729711311 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107023453511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_25 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83206426255127 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107025451519 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨25, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83206426255127 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107025451519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_26 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (1299564793639 / 1562500000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214054910737 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨26, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (1299564793639 / 1562500000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214054910737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_27 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41568945646317 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214058932497 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨27, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41568945646317 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214058932497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_28 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20775914930629 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107031455987 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨28, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20775914930629 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107031455987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_29 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (83069452050883 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (69189590923 / 3125000000000 : ℝ))
      (E := (cell13018 ⟨29, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (83069452050883 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (69189590923 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_30 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41517634123117 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214070926873 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨30, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41517634123117 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214070926873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_31 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (8300110827723 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (44281499309 / 2000000000000 : ℝ))
      (E := (cell13018 ⟨31, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (8300110827723 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (44281499309 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_32 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20741743028173 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (221407896791 / 10000000000000 : ℝ))
      (E := (cell13018 ⟨32, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20741743028173 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (221407896791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_33 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (25916518663 / 31250000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553520748451 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨33, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (25916518663 / 31250000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553520748451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_34 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (1295293298017 / 1562500000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214086985281 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨34, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (1295293298017 / 1562500000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214086985281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_35 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (1657294122729 / 2000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214091001489 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨35, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (1657294122729 / 2000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214091001489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_36 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16566132976227 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214094984079 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨36, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16566132976227 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214094984079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_37 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16559329455349 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (11070494959 / 500000000000 : ℝ))
      (E := (cell13018 ⟨37, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16559329455349 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (11070494959 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_38 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82762653293037 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214103024543 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨38, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82762653293037 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214103024543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_39 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (1034108536249 / 1250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276763377903 / 12500000000000 : ℝ))
      (E := (cell13018 ⟨39, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (1034108536249 / 1250000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276763377903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13019_20 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83378169850721 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213917021237 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨20, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83378169850721 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213917021237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_21 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (8334377010183 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442784210597 / 20000000000000 : ℝ))
      (E := (cell13019 ⟨21, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (8334377010183 / 10000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442784210597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_22 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83309394476489 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213925026299 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨22, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83309394476489 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213925026299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_23 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41637521471023 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106964530591 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨23, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41637521471023 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106964530591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_24 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (4162035773301 / 5000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213933043979 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨24, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (4162035773301 / 5000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213933043979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_25 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83206412016093 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106968547159 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨25, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83206412016093 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106968547159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_26 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20793033140029 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106970548991 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨26, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20793033140029 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106970548991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_27 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83137877066101 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106972528641 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨27, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83137877066101 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106972528641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_28 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (3324145820089 / 4000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213949091291 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨28, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (3324145820089 / 4000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213949091291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_29 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20767359459207 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213953084959 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨29, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20767359459207 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213953084959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_30 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83035254038411 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (138372318653 / 6250000000000 : ℝ))
      (E := (cell13019 ⟨30, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83035254038411 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (138372318653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_31 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (83001094075633 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213961133223 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨31, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (83001094075633 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213961133223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_32 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82966957917317 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213965131927 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨32, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82966957917317 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213965131927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_33 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (2073321138311 / 2500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213969154113 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨33, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (2073321138311 / 2500000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213969154113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_34 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82898756890139 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213973141927 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨34, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82898756890139 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213973141927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_35 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82864691959707 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106988577259 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨35, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82864691959707 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106988577259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_36 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (1294228917353 / 1562500000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (110699059611 / 5000000000000 : ℝ))
      (E := (cell13019 ⟨36, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (1294228917353 / 1562500000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (110699059611 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_37 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82796633112397 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213985196441 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨37, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82796633112397 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213985196441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_38 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82762639134879 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213989166999 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨38, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82762639134879 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213989166999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_39 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20682167186987 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213993221001 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨39, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20682167186987 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2213993221001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13020_20 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83378155582539 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213803229039 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨20, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83378155582539 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213803229039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_21 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83343755839927 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213807198189 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨21, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83343755839927 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213807198189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_22 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41654690110429 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213811225617 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨22, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41654690110429 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213811225617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_23 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83275028692683 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213815256329 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨23, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83275028692683 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213815256329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_24 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83240701222919 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442763847 / 20000000000 : ℝ))
      (E := (cell13020 ⟨24, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83240701222919 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442763847 / 20000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_25 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (332825591117 / 400000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213823281259 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨25, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (332825591117 / 400000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213823281259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_26 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20793029582381 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213827280891 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨26, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20793029582381 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213827280891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_27 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20784465710439 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213831294677 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨27, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20784465710439 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213831294677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_28 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83103631284121 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213835266273 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨28, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83103631284121 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213835266273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_29 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (64897987207 / 78125000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213839314567 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨29, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (64897987207 / 78125000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213839314567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_30 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83035239832773 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213843324233 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨30, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83035239832773 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213843324233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_31 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (83001079876221 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213847296663 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨31, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (83001079876221 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213847296663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_32 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (663735549793 / 800000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106925675101 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨32, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (663735549793 / 800000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106925675101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_33 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82932831345463 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (221385531009 / 10000000000000 : ℝ))
      (E := (cell13020 ⟨33, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82932831345463 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (221385531009 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_34 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20724685677343 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106929676439 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨34, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20724685677343 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106929676439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_35 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (10358084723143 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213863361877 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨35, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (10358084723143 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213863361877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_36 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82830636542229 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (44277346747 / 2000000000000 : ℝ))
      (E := (cell13020 ⟨36, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82830636542229 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (44277346747 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_37 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20699154737557 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106935698377 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨37, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20699154737557 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106935698377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_38 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82762624978899 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106937681929 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨38, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82762624978899 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106937681929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_39 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (10341081824769 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213879414453 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨39, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (10341081824769 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213879414453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13021_20 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83378141316551 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (885475773 / 40000000000 : ℝ))
      (E := (cell13021 ⟨20, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83378141316551 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (885475773 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_21 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10417967697527 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106846727859 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨21, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10417967697527 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106846727859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_22 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (4165468298371 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213697478951 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨22, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (4165468298371 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213697478951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_23 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10409376805689 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442740289427 / 20000000000000 : ℝ))
      (E := (cell13021 ⟨23, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10409376805689 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442740289427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_24 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83240686982009 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442741096017 / 20000000000000 : ℝ))
      (E := (cell13021 ⟨24, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83240686982009 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442741096017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_25 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20801595886149 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213709463863 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨25, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20801595886149 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213709463863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_26 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83172104101121 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106856729731 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨26, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83172104101121 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106856729731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_27 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41568924309799 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (138357341829 / 6250000000000 : ℝ))
      (E := (cell13021 ⟨27, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41568924309799 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (138357341829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_28 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20775904267051 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276715186927 / 12500000000000 : ℝ))
      (E := (cell13021 ⟨28, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20775904267051 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276715186927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_29 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83069409415277 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106862769921 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨29, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83069409415277 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106862769921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_30 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (2075880640733 / 2500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553432386421 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨30, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (2075880640733 / 2500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553432386421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_31 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (83001065678993 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213733514337 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨31, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (83001065678993 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213733514337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_32 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20741732383279 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106868782073 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨32, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20741732383279 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106868782073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_33 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20733204290167 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213741578963 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨33, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20733204290167 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213741578963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_34 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (16579745706157 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213745559501 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨34, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (16579745706157 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213745559501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_35 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82864663612761 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553437391227 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨35, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82864663612761 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553437391227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_36 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20707655594011 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213753595519 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨36, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20707655594011 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213753595519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_37 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82796604790237 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (110687879637 / 5000000000000 : ℝ))
      (E := (cell13021 ⟨37, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82796604790237 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (110687879637 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_38 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10345326353137 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106880807561 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨38, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10345326353137 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106880807561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_39 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20682160112633 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (110688280179 / 5000000000000 : ℝ))
      (E := (cell13021 ⟨39, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20682160112633 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (110688280179 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13022_20 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (20844531763189 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213575689929 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨20, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (20844531763189 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213575689929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_21 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83343727322699 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106789854453 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨21, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83343727322699 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106789854453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_22 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41654675858087 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213583669589 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨22, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41654675858087 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213583669589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_23 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83275000200531 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213587691983 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨23, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83275000200531 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213587691983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_24 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83240672743289 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (17293685319 / 781250000000 : ℝ))
      (E := (cell13022 ⟨24, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83240672743289 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (17293685319 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_25 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83206369312131 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553398925139 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨25, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83206369312131 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553398925139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_26 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41586044937453 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213599750597 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨26, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41586044937453 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213599750597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_27 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (83137834399627 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213603756461 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨27, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (83137834399627 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213603756461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_28 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (10387950356809 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106803860113 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨28, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (10387950356809 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106803860113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_29 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (4153469760389 / 5000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106805880391 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨29, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (4153469760389 / 5000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106805880391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_30 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (20758802857013 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106807881401 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨30, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (20758802857013 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106807881401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_31 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (20750262870987 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106809893123 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨31, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (20750262870987 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106809893123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_32 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82966915344289 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213623773759 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨32, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82966915344289 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213623773759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_33 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41466401489027 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213627784893 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨33, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41466401489027 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213627784893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_34 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82898714354379 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213631820431 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨34, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82898714354379 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213631820431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_35 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41432324721279 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (221363582227 / 10000000000000 : ℝ))
      (E := (cell13022 ⟨35, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41432324721279 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (221363582227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_36 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41415304106019 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213639849361 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨36, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41415304106019 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213639849361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_37 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82796590632423 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213643843107 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨37, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82796590632423 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213643843107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_38 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (8276259667347 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (110682393103 / 5000000000000 : ℝ))
      (E := (cell13022 ⟨38, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (8276259667347 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (110682393103 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_39 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (1292634786017 / 1562500000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442730369427 / 20000000000000 : ℝ))
      (E := (cell13022 ⟨39, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (1292634786017 / 1562500000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442730369427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13023_20 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16675622558231 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106730971509 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨20, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16675622558231 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106730971509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_21 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83343713067373 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553366489439 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨21, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83343713067373 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553366489439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_22 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83309337467119 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213469972603 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨22, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83309337467119 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213469972603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_23 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83274985957741 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106736966247 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨23, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83274985957741 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106736966247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_24 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83240658506759 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213477957243 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨24, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83240658506759 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213477957243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_25 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16641271016371 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (110674099567 / 5000000000000 : ℝ))
      (E := (cell13023 ⟨25, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16641271016371 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (110674099567 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_26 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41586037825439 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213485978949 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨26, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41586037825439 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213485978949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_27 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83137820181843 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553372495213 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨27, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83137820181843 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553372495213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_28 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83103588642927 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213493999199 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨28, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83103588642927 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213493999199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_29 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83069381002467 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276687254489 / 12500000000000 : ℝ))
      (E := (cell13023 ⟨29, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83069381002467 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276687254489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_30 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (83035197228967 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106751017067 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨30, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (83035197228967 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106751017067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_31 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16600207458217 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213506053827 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨31, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16600207458217 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213506053827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_32 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82966901157643 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442702007527 / 20000000000000 : ℝ))
      (E := (cell13023 ⟨32, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82966901157643 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442702007527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_33 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82932788797621 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213514045109 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨33, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82932788797621 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213514045109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_34 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82898700180153 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106759038517 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨34, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82898700180153 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106759038517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_35 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82864635274533 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553380518827 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨35, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82864635274533 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553380518827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_36 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (8283059405021 / 10000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106763049439 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨36, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (8283059405021 / 10000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106763049439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_37 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82796576476787 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (44270601783 / 2000000000000 : ℝ))
      (E := (cell13023 ⟨37, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82796576476787 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (44270601783 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_38 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (4138129126201 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (88541364187 / 4000000000000 : ℝ))
      (E := (cell13023 ⟨38, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (4138129126201 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (88541364187 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_39 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82728612161819 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213538145123 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨39, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82728612161819 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213538145123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13024_20 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83378098531747 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213348250077 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨20, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83378098531747 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213348250077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_21 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (520898117589 / 625000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213352202267 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨21, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (520898117589 / 625000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213352202267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_22 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16661864644051 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106678106461 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨22, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16661864644051 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106678106461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_23 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83274971717141 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276670028381 / 12500000000000 : ℝ))
      (E := (cell13024 ⟨23, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83274971717141 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276670028381 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_24 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83240644272417 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106682123861 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨24, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83240644272417 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106682123861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_25 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41603170426883 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221336827779 / 10000000000000 : ℝ))
      (E := (cell13024 ⟨25, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41603170426883 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221336827779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_26 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41586030714519 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276671532677 / 12500000000000 : ℝ))
      (E := (cell13024 ⟨26, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41586030714519 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276671532677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_27 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41568902983123 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213376259383 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨27, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41568902983123 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213376259383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_28 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41551787216783 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213380273841 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨28, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41551787216783 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213380273841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_29 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (83069366799339 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213384306709 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨29, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (83069366799339 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213384306709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_30 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16607036606413 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442677660227 / 20000000000000 : ℝ))
      (E := (cell13024 ⟨30, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16607036606413 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442677660227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_31 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16600204620081 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106696158539 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨31, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16600204620081 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106696158539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_32 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82966886973179 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553349088943 / 25000000000000 : ℝ))
      (E := (cell13024 ⟨32, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82966886973179 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553349088943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_33 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (10366596827421 / 12500000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213400359611 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨33, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (10366596827421 / 12500000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213400359611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_34 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41449343004053 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213404329311 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨34, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41449343004053 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213404329311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_35 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82864621108687 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213408382679 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨35, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82864621108687 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213408382679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_36 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (129422781079 / 156250000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213412344069 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨36, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (129422781079 / 156250000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213412344069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_37 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82796562323327 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276677048697 / 12500000000000 : ℝ))
      (E := (cell13024 ⟨37, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82796562323327 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276677048697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_38 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16552513675349 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106710200849 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨38, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16552513675349 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106710200849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_39 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (20682149505181 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442684876007 / 20000000000000 : ℝ))
      (E := (cell13024 ⟨39, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (20682149505181 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442684876007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

end BstLean.Part268
