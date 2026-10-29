import BstLean.Part268CellShard11Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12625_20 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41690926400579 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452170984459 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨20, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41690926400579 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452170984459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_21 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10418418289963 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260858925933 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨21, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10418418289963 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260858925933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_22 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (20828216027589 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260862912827 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨22, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (20828216027589 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260862912827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_23 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (16655681228033 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130433443429 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨23, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (16655681228033 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130433443429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_24 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83243972376353 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452174182007 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨24, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83243972376353 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452174182007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_25 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (8320956278631 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130437463723 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨25, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (8320956278631 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130437463723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_26 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10396897167199 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452175776771 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨26, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10396897167199 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452175776771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_27 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83140815997923 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260882899001 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨27, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83140815997923 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260882899001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_28 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10388309841899 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260886917201 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨28, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10388309841899 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260886917201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_29 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (20768041379363 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260890940931 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨29, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (20768041379363 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260890940931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_30 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (2075946907823 / 2500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260894913927 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨30, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (2075946907823 / 2500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260894913927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_31 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41501805544987 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (282612362083 / 12500000000000 : ℝ))
      (E := (cell12625 ⟨31, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41501805544987 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (282612362083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_32 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (16593873963431 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565225722731 / 25000000000000 : ℝ))
      (E := (cell12625 ⟨32, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (16593873963431 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565225722731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_33 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82935152463163 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (282613362283 / 12500000000000 : ℝ))
      (E := (cell12625 ⟨33, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82935152463163 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (282613362283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_34 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82900958996857 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452182184003 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨34, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82900958996857 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452182184003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_35 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82866789387257 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130457449327 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨35, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82866789387257 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130457449327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_36 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82832643603537 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260918952283 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨36, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82832643603537 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260918952283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_37 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82798521615029 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (141307681601 / 6250000000000 : ℝ))
      (E := (cell12625 ⟨37, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82798521615029 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (141307681601 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_38 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41382211695611 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260926935019 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨38, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41382211695611 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260926935019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_39 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41365174450879 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130465461669 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨39, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41365174450879 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130465461669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12626_20 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41690921933337 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (9042917821 / 400000000000 : ℝ))
      (E := (cell12626 ⟨20, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41690921933337 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (9042917821 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_21 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20836834424813 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260733435297 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨21, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20836834424813 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260733435297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_22 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83312855803499 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260737457629 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨22, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83312855803499 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260737457629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_23 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41639199073233 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260741467859 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨23, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41639199073233 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260741467859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_24 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (665951717563 / 800000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260745469627 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨24, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (665951717563 / 800000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260745469627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_25 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83209555417617 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260749466343 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨25, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83209555417617 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260749466343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_26 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (332700681123 / 400000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260753461177 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨26, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (332700681123 / 400000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260753461177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_27 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41570404626249 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260757457069 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨27, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41570404626249 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260757457069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_28 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83106472300751 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (565190364181 / 25000000000000 : ℝ))
      (E := (cell12626 ⟨28, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83106472300751 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (565190364181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_29 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83072159393563 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (282595682827 / 12500000000000 : ℝ))
      (E := (cell12626 ⟨29, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83072159393563 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (282595682827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_30 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (5189866906197 / 6250000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260769476987 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨30, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (5189866906197 / 6250000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260769476987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_31 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (10375450698237 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260773443323 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨31, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (10375450698237 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260773443323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_32 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82969364622337 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (56519437011 / 2500000000000 : ℝ))
      (E := (cell12626 ⟨32, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82969364622337 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (56519437011 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_33 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (10366893447147 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260781472813 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨33, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (10366893447147 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260781472813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_34 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41450477209637 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (22607854803 / 1000000000000 : ℝ))
      (E := (cell12626 ⟨34, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41450477209637 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (22607854803 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_35 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82866785117649 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260789445379 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨35, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82866785117649 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260789445379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_36 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82832639641479 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (45215869723 / 2000000000000 : ℝ))
      (E := (cell12626 ⟨36, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82832639641479 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (45215869723 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_37 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (2587453686253 / 3125000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130398742997 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨37, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (2587453686253 / 3125000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130398742997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_38 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20691105010747 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452160300793 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨38, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20691105010747 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452160300793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_39 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82730345859799 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260805481551 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨39, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82730345859799 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260805481551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12627_20 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41690917466919 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (113030202123 / 5000000000000 : ℝ))
      (E := (cell12627 ⟨20, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41690917466919 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (113030202123 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_21 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83347329080411 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260608057271 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨21, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83347329080411 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260608057271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_22 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41656423749107 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260612056811 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨22, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41656423749107 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260612056811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_23 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (832783901543 / 1000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (14128850281 / 625000000000 : ℝ))
      (E := (cell12627 ⟨23, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (832783901543 / 1000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (14128850281 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_24 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (20810989253973 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260620025361 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨24, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (20810989253973 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260620025361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_25 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41604774025191 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130312029903 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨25, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41604774025191 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130312029903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_26 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (5198447701583 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565157008679 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨26, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (5198447701583 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565157008679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_27 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (16628160501691 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260632011393 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨27, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (16628160501691 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260632011393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_28 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41553232933827 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260636051001 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨28, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41553232933827 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260636051001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_29 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (4153607663549 / 5000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130320019559 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨29, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (4153607663549 / 5000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130320019559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_30 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83037864686651 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260644036421 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨30, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83037864686651 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260644036421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_31 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83003600083047 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565162011231 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨31, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83003600083047 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565162011231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_32 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (8296935942871 / 10000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260652066409 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨32, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (8296935942871 / 10000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260652066409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_33 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82935142692343 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260656043853 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨33, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82935142692343 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260656043853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_34 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82900949842807 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130330018557 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨34, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82900949842807 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130330018557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_35 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82866780849121 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130332023647 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨35, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82866780849121 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130332023647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_36 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82832635680463 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565167018817 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨36, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82832635680463 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565167018817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_37 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41399257153083 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130336031509 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨37, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41399257153083 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130336031509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_38 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82764416695721 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260676069593 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨38, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82764416695721 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260676069593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_39 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82730342818769 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452136007297 / 20000000000000 : ℝ))
      (E := (cell12627 ⟨39, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82730342818769 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452136007297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12628_20 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83381826002649 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260478683927 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨20, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83381826002649 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260478683927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_21 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83347320463179 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226048267527 / 10000000000000 : ℝ))
      (E := (cell12628 ⟨21, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83347320463179 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226048267527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_22 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83312839194501 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282560831507 / 12500000000000 : ℝ))
      (E := (cell12628 ⟨22, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83312839194501 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282560831507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_23 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (20819595540917 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130245338253 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨23, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (20819595540917 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130245338253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_24 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16648789867581 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (5651236589 / 250000000000 : ℝ))
      (E := (cell12628 ⟨24, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16648789867581 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (5651236589 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_25 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83209540684603 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260498649451 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨25, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83209540684603 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260498649451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_26 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (20793789042831 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282562832861 / 12500000000000 : ℝ))
      (E := (cell12628 ⟨26, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (20793789042831 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282562832861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_27 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (2598149867681 / 3125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (35320416857 / 1562500000000 : ℝ))
      (E := (cell12628 ⟨27, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (2598149867681 / 3125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (35320416857 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_28 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83106459435899 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260510641577 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨28, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83106459435899 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260510641577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_29 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83072147149701 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (56512866761 / 2500000000000 : ℝ))
      (E := (cell12628 ⟨29, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83072147149701 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (56512866761 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_30 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83037858875417 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260518650737 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨30, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83037858875417 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260518650737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_31 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83003594581427 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (113026132147 / 5000000000000 : ℝ))
      (E := (cell12628 ⟨31, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83003594581427 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (113026132147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_32 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (20742338559069 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260526648829 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨32, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (20742338559069 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260526648829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_33 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16587027561733 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260530669959 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨33, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16587027561733 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260530669959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_34 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (323831817451 / 390625000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260534649057 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨34, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (323831817451 / 390625000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260534649057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_35 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82866776581671 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (5651346761 / 250000000000 : ℝ))
      (E := (cell12628 ⟨35, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82866776581671 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (5651346761 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_36 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (10354078965061 / 12500000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (17660489539 / 781250000000 : ℝ))
      (E := (cell12628 ⟨36, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (10354078965061 / 12500000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (17660489539 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_37 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82798510653241 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452109339071 / 20000000000000 : ℝ))
      (E := (cell12628 ⟨37, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82798510653241 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452109339071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_38 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (4138220667471 / 5000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130275345299 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨38, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (4138220667471 / 5000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130275345299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_39 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82730339778669 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260554705573 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨39, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82730339778669 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260554705573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12629_20 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83381817073109 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260353321379 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨20, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83381817073109 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260353321379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_21 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83347311847557 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260357347589 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨21, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83347311847557 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260357347589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_22 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41656415446179 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452072260337 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨22, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41656415446179 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452072260337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_23 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (10409796771821 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565091326039 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨23, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (10409796771821 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565091326039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_24 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20810985415353 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260369300347 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨24, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20810985415353 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260369300347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_25 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83209533320281 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260373293667 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨25, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83209533320281 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260373293667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_26 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83175149118739 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565094336423 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨26, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83175149118739 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565094336423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_27 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (8314078902451 / 10000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260381342563 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨27, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (8314078902451 / 10000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260381342563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_28 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83106453005487 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260385345369 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨28, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83106453005487 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260385345369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_29 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83072141029727 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260389298099 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨29, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83072141029727 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260389298099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_30 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83037853065449 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (4414830703 / 195312500000 : ℝ))
      (E := (cell12629 ⟨30, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83037853065449 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (4414830703 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_31 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83003589081037 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260397354429 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨31, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83003589081037 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260397354429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_32 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (10371168630629 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260401344809 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨32, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (10371168630629 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260401344809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_33 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82935132926139 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452081070227 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨33, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82935132926139 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452081070227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_34 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41450470346611 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260409316131 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨34, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41450470346611 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260409316131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_35 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (828667723153 / 1000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565103339519 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨35, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (828667723153 / 1000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565103339519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_36 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41416313880777 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260417360619 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨36, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41416313880777 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260417360619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_37 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82798507001319 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113021066217 / 5000000000000 : ℝ))
      (E := (cell12629 ⟨37, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82798507001319 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113021066217 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_38 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (16552882000817 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130212683491 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨38, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (16552882000817 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130212683491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_39 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82730336739497 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130214685693 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨39, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82730336739497 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130214685693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12630_20 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (1302840752269 / 1562500000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260228013089 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨20, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (1302840752269 / 1562500000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260228013089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_21 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83347303233543 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452046403187 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨21, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83347303233543 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452046403187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_22 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41656411295893 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260236005697 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨22, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41656411295893 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260236005697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_23 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83278366187001 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260240044593 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨23, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83278366187001 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260240044593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_24 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83243933986413 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565061004901 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨24, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83243933986413 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565061004901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_25 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (10401190744677 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260248050841 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨25, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (10401190744677 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260248050841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_26 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83175142067571 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (28253150309 / 1250000000000 : ℝ))
      (E := (cell12630 ⟨26, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83175142067571 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (28253150309 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_27 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83140782284607 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260256002539 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨27, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83140782284607 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260256002539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_28 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83106446576417 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260260045461 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨28, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83106446576417 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260260045461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_29 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83072134911057 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130132019531 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨29, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83072134911057 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130132019531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_30 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20759461814187 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260268044017 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨30, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20759461814187 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260268044017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_31 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (132805733731 / 160000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452054400761 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨31, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (132805733731 / 160000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452054400761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_32 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82969343854979 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452055207449 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨32, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82969343854979 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452055207449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_33 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82935128044767 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565070007201 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨33, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82935128044767 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565070007201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_34 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82900936120103 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260284038337 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨34, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82900936120103 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260284038337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_35 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82866768050007 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130144033473 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨35, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82866768050007 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130144033473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_36 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82832623803661 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130146028427 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨36, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82832623803661 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130146028427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_37 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (25874532297 / 31250000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141268504207 / 6250000000000 : ℝ))
      (E := (cell12630 ⟨37, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (25874532297 / 31250000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141268504207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_38 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16552881331943 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565075010013 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨38, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16552881331943 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565075010013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_39 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41365166850627 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130152016961 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨39, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41365166850627 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130152016961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12631_20 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83381799218969 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (113005137953 / 5000000000000 : ℝ))
      (E := (cell12631 ⟨20, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83381799218969 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (113005137953 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_21 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41673647310569 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260106738603 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨21, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41673647310569 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260106738603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_22 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (5207050893299 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130055382047 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨22, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (5207050893299 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130055382047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_23 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41639179100483 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260114781137 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨23, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41639179100483 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260114781137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_24 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20810981578227 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130059367503 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨24, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20810981578227 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130059367503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_25 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41604759298003 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565030686453 / 25000000000000 : ℝ))
      (E := (cell12631 ⟨25, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41604759298003 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565030686453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_26 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41587567508911 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130063379191 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨26, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41587567508911 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130063379191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_27 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (16628155109217 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (70629086739 / 3125000000000 : ℝ))
      (E := (cell12631 ⟨27, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (16628155109217 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (70629086739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_28 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (5194152509293 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130067370927 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨28, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (5194152509293 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130067370927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_29 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83072128793691 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452027755273 / 20000000000000 : ℝ))
      (E := (cell12631 ⟨29, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83072128793691 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452027755273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_30 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41518920724657 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565035691119 / 25000000000000 : ℝ))
      (E := (cell12631 ⟨30, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41518920724657 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565035691119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_31 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83003578083941 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130073383329 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨31, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83003578083941 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130073383329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_32 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82969338666117 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260150784689 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨32, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82969338666117 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260150784689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_33 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20733780791137 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (282519345193 / 12500000000000 : ℝ))
      (E := (cell12631 ⟨33, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20733780791137 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (282519345193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_34 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82900931548099 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260158757077 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨34, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82900931548099 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260158757077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_35 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (1294793184153 / 1562500000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260162772387 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨35, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (1294793184153 / 1562500000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260162772387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_36 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (10354077480851 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130083404173 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨36, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (10354077480851 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130083404173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_37 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20699624925121 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260170806933 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨37, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20699624925121 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260170806933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_38 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (10345550414539 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260174768501 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨38, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (10345550414539 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260174768501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_39 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82730330663939 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130089405309 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨39, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82730330663939 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130089405309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12632_20 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83381790294369 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (225997755929 / 10000000000000 : ℝ))
      (E := (cell12632 ⟨20, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83381790294369 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (225997755929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_21 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83347286010341 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259981515593 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨21, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83347286010341 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259981515593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_22 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83312805995353 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259985518557 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨22, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83312805995353 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259985518557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_23 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41639175108231 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259989513787 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨23, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41639175108231 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259989513787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_24 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (325171557191 / 390625000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451998712657 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨24, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (325171557191 / 390625000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451998712657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_25 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83209511236051 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451999510749 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨25, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83209511236051 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451999510749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_26 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83175127969489 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (56500038667 / 2500000000000 : ℝ))
      (E := (cell12632 ⟨26, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83175127969489 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (56500038667 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_27 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83140768808941 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (113000277251 / 5000000000000 : ℝ))
      (E := (cell12632 ⟨27, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83140768808941 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (113000277251 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_28 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83106433722301 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260009551467 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨28, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83106433722301 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260009551467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_29 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (20768030669407 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (226001356849 / 10000000000000 : ℝ))
      (E := (cell12632 ⟨29, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (20768030669407 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (226001356849 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_30 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (10379729455393 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130008769911 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨30, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (10379729455393 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130008769911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_31 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16600714517447 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282502690741 / 12500000000000 : ℝ))
      (E := (cell12632 ⟨31, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16600714517447 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282502690741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_32 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16593866695689 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260025528589 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨32, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16593866695689 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260025528589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_33 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41467559142741 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452005909871 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨33, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41467559142741 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452005909871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_34 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (8290092697721 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260033530949 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨34, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (8290092697721 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260033530949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_35 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41433379761327 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260037533023 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨35, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41433379761327 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260037533023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_36 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16566523178199 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (70626298639 / 3125000000000 : ℝ))
      (E := (cell12632 ⟨36, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16566523178199 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (70626298639 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_37 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (8279849605157 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130022771601 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨37, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (8279849605157 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130022771601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_38 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82764399973873 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260049552331 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨38, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82764399973873 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260049552331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_39 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (2585322738361 / 3125000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130026792019 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨39, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (2585322738361 / 3125000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130026792019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12633_20 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16676356274283 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282481544439 / 12500000000000 : ℝ))
      (E := (cell12633 ⟨20, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16676356274283 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282481544439 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_21 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83347277401151 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225985634691 / 10000000000000 : ℝ))
      (E := (cell12633 ⟨21, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83347277401151 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225985634691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_22 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (8331279769949 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225986032741 / 10000000000000 : ℝ))
      (E := (cell12633 ⟨22, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (8331279769949 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225986032741 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_23 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83278342233489 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225986435923 / 10000000000000 : ℝ))
      (E := (cell12633 ⟨23, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83278342233489 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225986435923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_24 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83243910970377 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129934164673 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨24, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83243910970377 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129934164673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_25 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83209503877551 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129936178933 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨25, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83209503877551 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129936178933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_26 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41587560461287 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259876331203 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨26, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41587560461287 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259876331203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_27 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83140762073177 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564970092273 / 25000000000000 : ℝ))
      (E := (cell12633 ⟨27, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83140762073177 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564970092273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_28 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16621285459451 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259884357383 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨28, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16621285459451 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259884357383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_29 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83072116562869 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129944178479 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨29, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83072116562869 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129944178479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_30 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83037829838241 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129946185027 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨30, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83037829838241 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129946185027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_31 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83003567091757 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564974085037 / 25000000000000 : ℝ))
      (E := (cell12633 ⟨31, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83003567091757 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564974085037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_32 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (20742332072991 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129950193027 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨32, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (20742332072991 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129950193027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_33 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (5183444587973 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (28248804903 / 1250000000000 : ℝ))
      (E := (cell12633 ⟨33, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (5183444587973 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (28248804903 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_34 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82900922407437 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259908359957 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨34, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82900922407437 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259908359957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_35 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41433377630297 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259912348857 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨35, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41433377630297 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259912348857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_36 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41416305968111 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225991635981 / 10000000000000 : ℝ))
      (E := (cell12633 ⟨36, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41416305968111 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225991635981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_37 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82798492403659 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259920393463 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨37, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82798492403659 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259920393463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_38 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (206910991581 / 250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282490548943 / 12500000000000 : ℝ))
      (E := (cell12633 ⟨38, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (206910991581 / 250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282490548943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_39 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (20682581148023 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129964177093 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨39, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (20682581148023 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129964177093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12634_20 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41690886225053 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564931801499 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨20, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41690886225053 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564931801499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_21 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83347268793569 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259731232551 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨21, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83347268793569 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259731232551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_22 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20828197351299 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (45194703813 / 2000000000000 : ℝ))
      (E := (cell12634 ⟨22, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20828197351299 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (45194703813 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_23 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83278334252047 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259739200781 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨23, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83278334252047 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259739200781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_24 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83243903301351 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451948641657 / 20000000000000 : ℝ))
      (E := (cell12634 ⟨24, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83243903301351 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451948641657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_25 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41604748260253 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259747216561 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨25, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41604748260253 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259747216561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_26 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (3327004555083 / 4000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259751228777 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨26, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (3327004555083 / 4000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259751228777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_27 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83140755338791 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564938797357 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨27, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83140755338791 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564938797357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_28 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (1662128417471 / 2000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129879609031 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨28, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (1662128417471 / 2000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129879609031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_29 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20768027612353 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259763200251 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨29, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20768027612353 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259763200251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_30 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41518912017301 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259767196667 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨30, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41518912017301 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259767196667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_31 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41501780798753 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564942802329 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨31, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41501780798753 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564942802329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_32 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82969323106671 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259775239977 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨32, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82969323106671 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259775239977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_33 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41467554265403 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259779231621 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨33, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41467554265403 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259779231621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_34 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82900917838777 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259783244101 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨34, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82900917838777 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259783244101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_35 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (8286675099961 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (141236701243 / 6250000000000 : ℝ))
      (E := (cell12634 ⟨35, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (8286675099961 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (141236701243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_36 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (10354075997811 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225979121843 / 10000000000000 : ℝ))
      (E := (cell12634 ⟨36, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (10354075997811 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225979121843 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_37 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (331193955027 / 400000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129897620187 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨37, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (331193955027 / 400000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129897620187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_38 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82764393291891 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129899613723 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨38, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82764393291891 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129899613723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_39 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (2068258038939 / 2500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (70618851203 / 3125000000000 : ℝ))
      (E := (cell12634 ⟨39, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (2068258038939 / 2500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (70618851203 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12635_20 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41690881765221 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129801055373 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨20, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41690881765221 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129801055373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_21 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41673630093797 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (90384244569 / 4000000000000 : ℝ))
      (E := (cell12635 ⟨21, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41673630093797 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (90384244569 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_22 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83312781112471 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259610108281 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨22, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83312781112471 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259610108281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_23 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (10409790784017 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451922819357 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨23, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (10409790784017 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451922819357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_24 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41621947816909 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259618083373 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨24, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41621947816909 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259618083373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_25 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16641897832983 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129811064917 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨25, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16641897832983 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129811064917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_26 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83175106832993 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259626122579 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨26, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83175106832993 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259626122579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_27 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (10392593575723 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259630122903 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨27, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (10392593575723 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259630122903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_28 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16621282890237 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129817066753 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨28, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16621282890237 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129817066753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_29 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41536052168629 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259638098371 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨29, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41536052168629 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259638098371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_30 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (20759454558057 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564910534169 / 25000000000000 : ℝ))
      (E := (cell12635 ⟨30, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (20759454558057 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564910534169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_31 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41501778052241 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259646133437 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨31, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41501778052241 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259646133437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_32 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (10371164740321 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259650090361 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨32, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (10371164740321 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259650090361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_33 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16587020731039 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259654126079 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨33, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16587020731039 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259654126079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_34 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (1295326769863 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129829062391 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨34, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (1295326769863 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129829062391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_35 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82866746739703 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259662146119 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨35, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82866746739703 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259662146119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_36 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82832604029793 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259666132313 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨36, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82832604029793 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259666132313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_37 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82798485110843 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (141229383913 / 6250000000000 : ℝ))
      (E := (cell12635 ⟨37, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82798485110843 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (141229383913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_38 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82764389952347 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259674118733 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨38, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82764389952347 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259674118733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_39 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16546063704791 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451935623907 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨39, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16546063704791 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451935623907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12636_20 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (10422719326553 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129738505743 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨20, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (10422719326553 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129738505743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_21 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (3333890063329 / 4000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129740525113 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨21, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (3333890063329 / 4000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129740525113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_22 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16662554564263 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129742510991 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨22, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16662554564263 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129742510991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_23 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16655663658751 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129744523621 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨23, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16655663658751 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129744523621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_24 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (2601371498993 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259493012977 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨24, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (2601371498993 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259493012977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_25 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83209481810777 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259497039297 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨25, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83209481810777 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259497039297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_26 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41587549895163 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (17652351661 / 781250000000 : ℝ))
      (E := (cell12636 ⟨26, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41587549895163 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (17652351661 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_27 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41570370937077 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451901010529 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨27, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41570370937077 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451901010529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_28 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (1038830100377 / 1250000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451901809051 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨28, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (1038830100377 / 1250000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451901809051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_29 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41536049113203 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129756525659 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨29, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41536049113203 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129756525659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_30 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41518906215559 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259517014561 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨30, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41518906215559 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259517014561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_31 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16600710122537 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259521053979 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨31, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16600710122537 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259521053979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_32 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41484656369827 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259525054311 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨32, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41484656369827 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259525054311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_33 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (1295860918449 / 1562500000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564882268903 / 25000000000000 : ℝ))
      (E := (cell12636 ⟨33, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (1295860918449 / 1562500000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564882268903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_34 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (103626135881 / 125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (11297665303 / 500000000000 : ℝ))
      (E := (cell12636 ⟨34, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (103626135881 / 125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (11297665303 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_35 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (10358342810109 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129768534463 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨35, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (10358342810109 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129768534463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_36 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41416300039069 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282442630351 / 12500000000000 : ℝ))
      (E := (cell12636 ⟨36, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41416300039069 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282442630351 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_37 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82798481465937 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451909008299 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨37, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82798481465937 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451909008299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_38 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41382193306883 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451909813081 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨38, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41382193306883 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451909813081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_39 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82730315491277 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (112977652801 / 5000000000000 : ℝ))
      (E := (cell12636 ⟨39, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82730315491277 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (112977652801 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12637_20 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83381745696049 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259352024769 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨20, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83381745696049 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259352024769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_21 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41673621490231 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129677991131 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨21, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41673621490231 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129677991131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_22 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (3332510581269 / 4000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129679995039 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨22, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (3332510581269 / 4000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129679995039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_23 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83278310316903 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564840998453 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨23, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83278310316903 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564840998453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_24 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41621940151613 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259367997099 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨24, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41621940151613 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259367997099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_25 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41604737229047 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259372003339 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨25, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41604737229047 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259372003339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_26 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41587546374537 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129688007847 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨26, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41587546374537 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129688007847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_27 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41570367571951 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564845009273 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨27, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41570367571951 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564845009273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_28 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41553200805237 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259384011773 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨28, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41553200805237 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259384011773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_29 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (10384011514607 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564847000153 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨29, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (10384011514607 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564847000153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_30 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83037806631273 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451878401169 / 20000000000000 : ℝ))
      (E := (cell12637 ⟨30, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83037806631273 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451878401169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_31 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41501772561057 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (90375841179 / 4000000000000 : ℝ))
      (E := (cell12637 ⟨31, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41501772561057 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (90375841179 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_32 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82969307557929 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564850003681 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨32, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82969307557929 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564850003681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_33 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20733773476857 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129702010823 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨33, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20733773476857 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129702010823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_34 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41450452069741 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129703996479 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨34, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41450452069741 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129703996479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_35 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41433369111559 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129706023467 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨35, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41433369111559 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129706023467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_36 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (517703725797 / 625000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259416008569 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨36, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (517703725797 / 625000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259416008569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_37 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (5174904863877 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129710027189 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨37, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (5174904863877 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129710027189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_38 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (1655287665523 / 2000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225942400877 / 10000000000000 : ℝ))
      (E := (cell12637 ⟨38, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (1655287665523 / 2000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225942400877 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_39 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41365156229763 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129714023977 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨39, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41365156229763 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129714023977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12638_20 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41690868390659 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129613517023 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨20, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41690868390659 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129613517023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_21 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (10418404297413 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90369241077 / 4000000000000 : ℝ))
      (E := (cell12638 ⟨21, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (10418404297413 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90369241077 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_22 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (10414094530463 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451847002513 / 20000000000000 : ℝ))
      (E := (cell12638 ⟨22, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (10414094530463 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451847002513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_23 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (4163915117079 / 5000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129619497419 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨23, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (4163915117079 / 5000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129619497419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_24 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41621936320083 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112962151787 / 5000000000000 : ℝ))
      (E := (cell12638 ⟨24, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41621936320083 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112962151787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_25 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83209467106863 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129623510981 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨25, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83209467106863 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129623510981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_26 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41587542854619 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (70601594219 / 3125000000000 : ℝ))
      (E := (cell12638 ⟨26, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41587542854619 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (70601594219 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_27 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83140728415027 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (141203438613 / 6250000000000 : ℝ))
      (E := (cell12638 ⟨27, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83140728415027 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (141203438613 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_28 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (1298537424877 / 1562500000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259259033057 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨28, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (1298537424877 / 1562500000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259259033057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_29 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83072086008607 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (35300984449 / 1562500000000 : ℝ))
      (E := (cell12638 ⟨29, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83072086008607 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (35300984449 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_30 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83037800832691 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129633496757 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨30, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83037800832691 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129633496757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_31 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83003539632769 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451854200279 / 20000000000000 : ℝ))
      (E := (cell12638 ⟨31, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83003539632769 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451854200279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_32 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (5185581398587 / 6250000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259275030153 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨32, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (5185581398587 / 6250000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259275030153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_33 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82935089035271 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129639511379 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨33, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82935089035271 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129639511379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_34 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82900899575277 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259283039057 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨34, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82900899575277 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259283039057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_35 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41433366983219 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259287021521 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨35, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41433366983219 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259287021521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_36 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82832592177941 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259291029593 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨36, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82832592177941 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259291029593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_37 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (10349809272391 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564823765979 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨37, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (10349809272391 / 12500000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564823765979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_38 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82764379939497 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (282412383277 / 12500000000000 : ℝ))
      (E := (cell12638 ⟨38, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82764379939497 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (282412383277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_39 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (827303094287 / 1000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112965151831 / 5000000000000 : ℝ))
      (E := (cell12638 ⟨39, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (827303094287 / 1000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112965151831 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12639_20 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83381727868231 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259102039319 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨20, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83381727868231 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259102039319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_21 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (10418403222469 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129553033811 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨21, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (10418403222469 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129553033811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_22 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83312747957249 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259110031127 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨22, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83312747957249 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259110031127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_23 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83278294367787 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129557025159 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨23, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83278294367787 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129557025159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_24 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41621932489299 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259118070533 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨24, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41621932489299 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259118070533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_25 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (16641891951417 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (282390254597 / 12500000000000 : ℝ))
      (E := (cell12639 ⟨25, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (16641891951417 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (282390254597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_26 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (2599221208463 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259126068967 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨26, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (2599221208463 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259126068967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_27 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (10392590210941 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (225913005323 / 10000000000000 : ℝ))
      (E := (cell12639 ⟨27, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (10392590210941 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (225913005323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_28 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83106388775121 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259134050649 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨28, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83106388775121 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259134050649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_29 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83072079901659 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (225913806369 / 10000000000000 : ℝ))
      (E := (cell12639 ⟨29, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83072079901659 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (225913806369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_30 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (20759448758843 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259142094583 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨30, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (20759448758843 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259142094583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_31 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83003534144649 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (5647865217 / 250000000000 : ℝ))
      (E := (cell12639 ⟨31, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83003534144649 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (5647865217 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_32 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82969297198043 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451830008409 / 20000000000000 : ℝ))
      (E := (cell12639 ⟨32, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82969297198043 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451830008409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_33 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (10366885520533 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564788519737 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨33, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (10366885520533 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564788519737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_34 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (16580179002437 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (70598690053 / 3125000000000 : ℝ))
      (E := (cell12639 ⟨34, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (16580179002437 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (70598690053 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_35 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (16573345942167 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259162051309 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨35, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (16573345942167 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259162051309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_36 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (414162941147 / 500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259166105881 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨36, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (414162941147 / 500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259166105881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_37 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (3311938821489 / 4000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259170070109 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨37, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (3311938821489 / 4000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259170070109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_38 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (2586386768869 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259174061661 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨38, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (2586386768869 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259174061661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_39 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82730306398801 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129589040367 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨39, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82730306398801 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129589040367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12640_20 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83381718956787 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141186072321 / 6250000000000 : ℝ))
      (E := (cell12640 ⟨20, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83381718956787 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141186072321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_21 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20836804295451 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129490581327 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨21, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20836804295451 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129490581327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_22 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83312739672361 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129492581203 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨22, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83312739672361 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129492581203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_23 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83278286395521 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258989160261 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨23, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83278286395521 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258989160261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_24 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (2081096432963 / 2500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282374144981 / 12500000000000 : ℝ))
      (E := (cell12640 ⟨24, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (2081096432963 / 2500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282374144981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_25 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83209452408759 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (451799432913 / 20000000000000 : ℝ))
      (E := (cell12640 ⟨25, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83209452408759 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (451799432913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_26 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83175071633809 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (56475027979 / 2500000000000 : ℝ))
      (E := (cell12640 ⟨26, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83175071633809 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (56475027979 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_27 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41570357480703 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259005143361 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨27, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41570357480703 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259005143361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_28 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20776595589863 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129504561507 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨28, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20776595589863 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129504561507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_29 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20768018449003 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129506588739 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨29, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20768018449003 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129506588739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_30 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20759447309829 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259017133533 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨30, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20759447309829 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259017133533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_31 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (16600705731551 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259021168633 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨31, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (16600705731551 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259021168633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_32 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82969292019881 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282378145939 / 12500000000000 : ℝ))
      (E := (cell12640 ⟨32, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82969292019881 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282378145939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_33 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82935079294407 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564757282911 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨33, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82935079294407 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564757282911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_34 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (16580178090041 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259033179479 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨34, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (16580178090041 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259033179479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_35 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41433362728153 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141189821019 / 6250000000000 : ℝ))
      (E := (cell12640 ⟨35, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41433362728153 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141189821019 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_36 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82832584281897 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259041178789 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨36, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82832584281897 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259041178789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_37 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41399233448161 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129522595151 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨37, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41399233448161 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129522595151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_38 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82764373269081 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282381146399 / 12500000000000 : ℝ))
      (E := (cell12640 ⟨38, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82764373269081 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282381146399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_39 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20682575842457 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259053180301 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨39, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20682575842457 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259053180301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12641_20 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16676342009397 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282356533869 / 12500000000000 : ℝ))
      (E := (cell12641 ⟨20, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16676342009397 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282356533869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_21 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83347208585461 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564714063431 / 25000000000000 : ℝ))
      (E := (cell12641 ⟨21, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83347208585461 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564714063431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_22 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83312731389039 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258860289761 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨22, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83312731389039 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258860289761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_23 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (5204892401549 / 6250000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258864266317 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨23, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (5204892401549 / 6250000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258864266317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_24 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83243849659931 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129434122659 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨24, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83243849659931 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129434122659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_25 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16641889012377 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564718072137 / 25000000000000 : ℝ))
      (E := (cell12641 ⟨25, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16641889012377 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564718072137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_26 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (10396883074777 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258876282411 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨26, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (10396883074777 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258876282411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_27 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (4157035411833 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (11294401441 / 500000000000 : ℝ))
      (E := (cell12641 ⟨27, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (4157035411833 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (11294401441 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_28 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41553187972561 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564721062537 / 25000000000000 : ℝ))
      (E := (cell12641 ⟨28, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41553187972561 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564721062537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_29 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41536033845833 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129444143807 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨29, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41536033845833 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129444143807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_30 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83037783444523 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129446142943 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨30, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83037783444523 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129446142943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_31 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41501761586043 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258896246891 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨31, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41501761586043 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258896246891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_32 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82969286842907 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129450144721 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨32, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82969286842907 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129450144721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_33 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (829350744257 / 1000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129452148999 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨33, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (829350744257 / 1000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129452148999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_34 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41450442944669 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258908273803 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨34, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41450442944669 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258908273803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_35 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (20716680300713 / 25000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258912276503 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨35, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (20716680300713 / 25000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258912276503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_36 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82832580335431 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258916306963 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨36, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82832580335431 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258916306963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_37 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82798463256419 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258920307153 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨37, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82798463256419 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258920307153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_38 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82764369935317 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129462138709 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨38, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82764369935317 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129462138709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_39 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (4136515017089 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129464138301 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨39, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (4136515017089 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129464138301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12642_20 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41690850569413 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (7058523247 / 312500000000 : ℝ))
      (E := (cell12642 ⟨20, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41690850569413 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (7058523247 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_21 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41673599995361 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282341424891 / 12500000000000 : ℝ))
      (E := (cell12642 ⟨21, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41673599995361 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282341424891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_22 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83312723107283 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451747082639 / 20000000000000 : ℝ))
      (E := (cell12642 ⟨22, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83312723107283 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451747082639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_23 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41639135227787 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564684856709 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨23, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41639135227787 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564684856709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_24 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83243842002833 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258743443677 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨24, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83243842002833 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258743443677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_25 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83209437716463 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129373704363 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨25, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83209437716463 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129373704363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_26 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20793764391009 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258751441897 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨26, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20793764391009 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258751441897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_27 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (8314070151329 / 10000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258755429313 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨27, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (8314070151329 / 10000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258755429313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_28 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83106369532129 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282344929007 / 12500000000000 : ℝ))
      (E := (cell12642 ⟨28, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83106369532129 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282344929007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_29 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83072061588619 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258763452587 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨29, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83072061588619 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258763452587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_30 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83037777650993 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258767434627 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨30, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83037777650993 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258767434627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_31 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83003517687641 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258771438641 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨31, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83003517687641 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258771438641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_32 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (1037116020839 / 1250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451755093279 / 20000000000000 : ℝ))
      (E := (cell12642 ⟨32, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (1037116020839 / 1250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451755093279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_33 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41467534779071 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129389730429 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨33, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41467534779071 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129389730429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_34 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82900881329583 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282347927909 / 12500000000000 : ℝ))
      (E := (cell12642 ⟨34, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82900881329583 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (282347927909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_35 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82866716950473 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258787471909 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨35, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82866716950473 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258787471909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_36 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41416288195001 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258791431759 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨36, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41416288195001 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258791431759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_37 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20699614904379 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129397710331 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨37, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20699614904379 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129397710331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_38 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20691091650629 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564699859759 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨38, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20691091650629 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564699859759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_39 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82730297314657 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258803428357 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨39, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82730297314657 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258803428357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12643_20 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20845423058077 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225860260313 / 10000000000000 : ℝ))
      (E := (cell12643 ⟨20, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20845423058077 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225860260313 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_21 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41673595698793 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225860659887 / 10000000000000 : ℝ))
      (E := (cell12643 ⟨21, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41673595698793 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225860659887 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_22 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20828178706773 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564652662337 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨22, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20828178706773 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564652662337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_23 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20819565621973 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451722928363 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨23, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20819565621973 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451722928363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_24 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83243834347223 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451723727639 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨24, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83243834347223 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451723727639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_25 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20802357593123 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258622641881 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨25, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20802357593123 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258622641881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_26 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83175050531269 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (112931329881 / 5000000000000 : ℝ))
      (E := (cell12643 ⟨26, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83175050531269 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (112931329881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_27 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (16628138958259 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129315312569 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨27, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (16628138958259 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129315312569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_28 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41553181560237 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564658652569 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨28, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41553181560237 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564658652569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_29 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83072055486873 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225863861391 / 10000000000000 : ℝ))
      (E := (cell12643 ⟨29, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83072055486873 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (225863861391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_30 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20759442964681 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564660659567 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨30, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20759442964681 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564660659567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_31 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83003512204421 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129323313409 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨31, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83003512204421 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129323313409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_32 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82969276492519 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451730127963 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨32, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82969276492519 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451730127963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_33 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41467532345867 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258654620223 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨33, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41467532345867 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258654620223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_34 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82900876770939 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (141166164243 / 6250000000000 : ℝ))
      (E := (cell12643 ⟨34, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82900876770939 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (141166164243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_35 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (2589584771849 / 3125000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258662663899 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨35, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (2589584771849 / 3125000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258662663899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_36 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (8283257244561 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258666670471 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨36, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (8283257244561 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258666670471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_37 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20699613994903 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129335324087 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨37, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20699613994903 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129335324087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_38 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20691090817669 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (141167166003 / 6250000000000 : ℝ))
      (E := (cell12643 ⟨38, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20691090817669 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (141167166003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_39 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82730294288459 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129339317783 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨39, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82730294288459 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129339317783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12644_20 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83381683327431 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282309734971 / 12500000000000 : ℝ))
      (E := (cell12644 ⟨20, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83381683327431 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282309734971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_21 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41673591403027 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258481852949 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨21, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41673591403027 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258481852949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_22 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41656353274233 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258485881581 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨22, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41656353274233 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258485881581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_23 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (10409781815217 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129244926457 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨23, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (10409781815217 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129244926457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_24 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83243826693103 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258493887237 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨24, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83243826693103 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258493887237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_25 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83209423029971 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129248935617 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨25, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83209423029971 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129248935617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_26 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20793760874979 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564625466601 / 25000000000000 : ℝ))
      (E := (cell12644 ⟨26, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20793760874979 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564625466601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_27 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (3325627522827 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129252937837 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨27, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (3325627522827 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129252937837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_28 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16621271342031 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258509843271 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨28, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16621271342031 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258509843271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_29 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (3322881975457 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129256944277 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨29, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (3322881975457 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129256944277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_30 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83037766067717 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258517838299 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨30, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83037766067717 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258517838299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_31 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (3320140268897 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564630467489 / 25000000000000 : ℝ))
      (E := (cell12644 ⟨31, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (3320140268897 / 4000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564630467489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_32 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16593854263821 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129262934129 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨32, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16593854263821 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129262934129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_33 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41467529913237 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258529893251 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨33, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41467529913237 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258529893251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_34 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82900872213407 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258533887649 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨34, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82900872213407 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258533887649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_35 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (10358338556117 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282317231559 / 12500000000000 : ℝ))
      (E := (cell12644 ⟨35, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (10358338556117 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282317231559 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_36 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41416284251127 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129270952903 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨36, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41416284251127 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129270952903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_37 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20699613085677 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129272936173 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨37, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20699613085677 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129272936173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_38 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82764359939799 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258549869757 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨38, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82764359939799 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258549869757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_39 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41365145631593 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (225855389823 / 10000000000000 : ℝ))
      (E := (cell12644 ⟨39, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41365145631593 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (225855389823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12645_20 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20845418606049 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282294144051 / 12500000000000 : ℝ))
      (E := (cell12645 ⟨20, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20845418606049 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282294144051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_21 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20836793554031 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (225835710307 / 10000000000000 : ℝ))
      (E := (cell12645 ⟨21, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20836793554031 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (225835710307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_22 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20828174567851 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258361109897 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨22, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20828174567851 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258361109897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_23 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83278246557107 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258365118477 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨23, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83278246557107 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258365118477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_24 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (8324381904047 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258369132439 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨24, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (8324381904047 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258369132439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_25 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83209415688901 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (90334926207 / 4000000000000 : ℝ))
      (E := (cell12645 ⟨25, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83209415688901 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (90334926207 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_26 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41587518234987 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258377131427 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨26, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41587518234987 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258377131427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_27 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (8314068135143 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129190561243 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨27, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (8314068135143 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129190561243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_28 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41553175150587 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258385131041 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨28, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41553175150587 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258385131041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_29 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83072043287277 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258389159551 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨29, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83072043287277 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258389159551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_30 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83037760277971 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258393151737 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨30, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83037760277971 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258393151737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_31 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20750875310413 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258397168057 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨31, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20750875310413 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258397168057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_32 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82969266146877 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564600287931 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨32, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82969266146877 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564600287931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_33 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82935054962363 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129202581393 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨33, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82935054962363 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129202581393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_34 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (16580173531397 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129204571979 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨34, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (16580173531397 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129204571979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_35 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82866704199779 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129206577439 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨35, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82866704199779 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129206577439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_36 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (16566512911987 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564604284441 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨36, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (16566512911987 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564604284441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_37 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41399224353401 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258421151851 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨37, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41399224353401 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258421151851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_38 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82764356609883 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258425138861 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨38, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82764356609883 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258425138861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_39 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82730288238837 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (8821988897 / 390625000000 : ℝ))
      (E := (cell12645 ⟨39, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82730288238837 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (8821988897 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12646_20 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83381665522601 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451645684211 / 20000000000000 : ℝ))
      (E := (cell12646 ⟨20, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83381665522601 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451645684211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_21 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20836791406949 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225823246583 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨21, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20836791406949 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225823246583 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_22 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83312689995907 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451647290187 / 20000000000000 : ℝ))
      (E := (cell12646 ⟨22, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83312689995907 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451647290187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_23 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20819559648501 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129120219253 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨23, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20819559648501 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129120219253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_24 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41621905694663 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225824443217 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨24, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41621905694663 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225824443217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_25 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83209408349281 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258248435317 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨25, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83209408349281 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258248435317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_26 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (16635005888289 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (70570389097 / 3125000000000 : ℝ))
      (E := (cell12646 ⟨26, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (16635005888289 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (70570389097 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_27 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83140674633559 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129128212007 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨27, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83140674633559 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129128212007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_28 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83106343893529 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225826047359 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨28, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83106343893529 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225826047359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_29 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83072037189427 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129132213453 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨29, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83072037189427 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129132213453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_30 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41518877244743 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258268461571 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨30, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41518877244743 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258268461571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_31 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83003495762103 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225827246259 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨31, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83003495762103 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225827246259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_32 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (16593852195167 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129138215831 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨32, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (16593852195167 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129138215831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_33 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (414675250497 / 500000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258280428833 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨33, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (414675250497 / 500000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258280428833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_34 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41450431550837 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258284455417 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨34, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41450431550837 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258284455417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_35 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41433349975847 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129144226937 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨35, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41433349975847 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129144226937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_36 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82832560618651 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564573120911 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨36, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82832560618651 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564573120911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_37 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (16559689014379 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564574121673 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨37, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (16559689014379 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564574121673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_38 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82764353280929 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129150231681 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨38, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82764353280929 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129150231681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_39 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20682571303853 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258304472493 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨39, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20682571303853 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258304472493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12647_20 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41690828311323 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564525950563 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨20, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41690828311323 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564525950563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_21 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83347157041071 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (35282933849 / 1562500000000 : ℝ))
      (E := (cell12647 ⟨21, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83347157041071 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (35282933849 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_22 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41656340860987 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282263973507 / 12500000000000 : ℝ))
      (E := (cell12647 ⟨22, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41656340860987 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282263973507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_23 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41639115316213 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258115813001 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨23, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41639115316213 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258115813001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_24 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83243803739669 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564529946607 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨24, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83243803739669 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564529946607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_25 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83209401011111 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258123770049 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨25, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83209401011111 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258123770049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_26 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (10396877801791 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129063883509 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨26, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (10396877801791 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129063883509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_27 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41570333958531 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258131780257 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨27, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41570333958531 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258131780257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_28 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (4155316874361 / 5000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451627162491 / 20000000000000 : ℝ))
      (E := (cell12647 ⟨28, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (4155316874361 / 5000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451627162491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_29 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (664576248743 / 800000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258139807583 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨29, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (664576248743 / 800000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258139807583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_30 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41518874351131 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451628765261 / 20000000000000 : ℝ))
      (E := (cell12647 ⟨30, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41518874351131 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451628765261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_31 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (324232383921 / 390625000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282268476511 / 12500000000000 : ℝ))
      (E := (cell12647 ⟨31, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (324232383921 / 390625000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282268476511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_32 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41484627902989 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112907591259 / 5000000000000 : ℝ))
      (E := (cell12647 ⟨32, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41484627902989 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112907591259 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_33 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (5183440327349 / 6250000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451631161709 / 20000000000000 : ℝ))
      (E := (cell12647 ⟨33, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (5183440327349 / 6250000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451631161709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_34 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41450429273737 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282269977753 / 12500000000000 : ℝ))
      (E := (cell12647 ⟨34, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41450429273737 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282269977753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_35 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41433347852341 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258163808079 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨35, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41433347852341 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258163808079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_36 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82832556678403 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564541956537 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨36, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82832556678403 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564541956537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_37 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41399220718993 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564542954549 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨37, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41399220718993 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564542954549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_38 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16552869990587 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112908792163 / 5000000000000 : ℝ))
      (E := (cell12647 ⟨38, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16552869990587 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112908792163 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_39 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82730282192911 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564544960703 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨39, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82730282192911 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564544960703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12648_20 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83381647724331 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (35280924679 / 1562500000000 : ℝ))
      (E := (cell12648 ⟨20, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83381647724331 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (35280924679 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_21 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41673574227973 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257983179483 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨21, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41673574227973 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257983179483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_22 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83312673449603 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257987179583 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨22, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83312673449603 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257987179583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_23 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41639111336187 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112899559181 / 5000000000000 : ℝ))
      (E := (cell12648 ⟨23, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41639111336187 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112899559181 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_24 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (166487592183 / 200000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257995195217 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨24, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (166487592183 / 200000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257995195217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_25 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (8320939367439 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128999579687 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨25, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (8320939367439 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128999579687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_26 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41587507694311 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129001598001 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨26, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41587507694311 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129001598001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_27 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41570330600969 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258007191217 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨27, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41570330600969 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258007191217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_28 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83106331082247 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258011206099 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨28, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83106331082247 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258011206099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_29 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41536012498811 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258015184617 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨29, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41536012498811 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258015184617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_30 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41518871458149 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564504796859 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨30, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41518871458149 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564504796859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_31 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83003484806673 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (45160464331 / 2000000000000 : ℝ))
      (E := (cell12648 ⟨31, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83003484806673 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (45160464331 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_32 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41484625318653 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258027215171 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨32, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41484625318653 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258027215171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_33 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82935040376917 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258031184767 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨33, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82935040376917 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258031184767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_34 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (5181303374649 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258035185181 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨34, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (5181303374649 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258035185181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_35 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (10358336432343 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258039217497 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨35, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (10358336432343 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258039217497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_36 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (8283255273919 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (282255402991 / 12500000000000 : ℝ))
      (E := (cell12648 ⟨36, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (8283255273919 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (282255402991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_37 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (3311937512203 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564511801259 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨37, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (3311937512203 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564511801259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_38 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82764346625903 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112902560993 / 5000000000000 : ℝ))
      (E := (cell12648 ⟨38, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82764346625903 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112902560993 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_39 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41365139585667 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258055209871 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨39, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41365139585667 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258055209871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12649_20 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (16676327765531 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128927305471 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨20, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (16676327765531 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128927305471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_21 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83347139872423 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564464647169 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨21, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83347139872423 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564464647169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_22 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20828166294699 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257862625517 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨22, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20828166294699 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257862625517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_23 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83278214713847 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564466652177 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨23, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83278214713847 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564466652177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_24 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83243788444817 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257870600171 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨24, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83243788444817 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257870600171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_25 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41604693169559 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257874603293 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨25, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41604693169559 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257874603293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_26 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41587504182163 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257878621229 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨26, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41587504182163 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257878621229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_27 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83140654488187 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257882598459 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨27, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83140654488187 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257882598459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_28 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83106324678609 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257886596063 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨28, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83106324678609 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257886596063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_29 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41536009451833 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451578123299 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨29, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41536009451833 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451578123299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_30 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83037737131593 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (141118412717 / 6250000000000 : ℝ))
      (E := (cell12649 ⟨30, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83037737131593 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (141118412717 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_31 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83003479330791 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257898617449 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨31, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83003479330791 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257898617449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_32 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82969245469819 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257902601637 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨32, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82969245469819 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257902601637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_33 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20733758879349 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128953308041 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨33, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20733758879349 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128953308041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_34 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82900849442403 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564477650873 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨34, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82900849442403 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564477650873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_35 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82866687213877 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128957311753 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨35, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82866687213877 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128957311753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_36 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82832548801013 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128959309167 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨36, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82832548801013 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128959309167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_37 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41399217086581 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128961323607 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨37, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41399217086581 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128961323607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_38 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (8276434329983 / 10000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257926651861 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨38, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (8276434329983 / 10000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257926651861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_39 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (2068256903767 / 2500000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257930632391 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨39, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (2068256903767 / 2500000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257930632391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

end BstLean.Part268
