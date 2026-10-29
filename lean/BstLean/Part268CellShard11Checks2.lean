import BstLean.Part268CellShard11Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12625_40 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (5168518632277 / 6250000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130467464613 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨40, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (5168518632277 / 6250000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130467464613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_41 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82662271005193 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (8831792783 / 390625000000 : ℝ))
      (E := (cell12625 ⟨41, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82662271005193 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (8831792783 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_42 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41314133769071 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1766361667 / 78125000000 : ℝ))
      (E := (cell12625 ⟨42, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41314133769071 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1766361667 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_43 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (8259428768553 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130473465613 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨43, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (8259428768553 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130473465613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_44 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82560331417759 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260950943953 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨44, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82560331417759 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260950943953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_45 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (4126319935269 / 5000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260954970827 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨45, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (4126319935269 / 5000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260954970827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_46 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (8249248951909 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130479475821 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨46, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (8249248951909 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130479475821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_47 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41229301914869 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452192588737 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨47, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41229301914869 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452192588737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_48 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (16484948321663 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260966945197 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨48, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (16484948321663 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260966945197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_49 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (2059772570649 / 2500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130485477103 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨49, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (2059772570649 / 2500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130485477103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_50 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41178543726979 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130487484261 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨50, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41178543726979 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130487484261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_51 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41161647731867 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260978985747 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨51, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41161647731867 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260978985747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_52 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (4114476341343 / 5000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260983003267 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨52, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (4114476341343 / 5000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260983003267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_53 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82255781515049 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452197391843 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨53, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82255781515049 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452197391843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_54 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (20555514875039 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260990968623 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨54, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (20555514875039 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260990968623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_55 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (3287534430167 / 4000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260994969227 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨55, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (3287534430167 / 4000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260994969227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_56 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82154685249241 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565249754173 / 25000000000000 : ℝ))
      (E := (cell12625 ⟨56, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82154685249241 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565249754173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_57 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (8212103295763 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130501494573 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨57, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (8212103295763 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130501494573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_58 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10260925481469 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2261007000979 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨58, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10260925481469 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2261007000979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_59 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (82053797904159 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2261010989 / 100000000000 : ℝ))
      (E := (cell12625 ⟨59, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (82053797904159 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2261010989 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12626_40 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (3307851815213 / 4000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130404738703 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨40, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (3307851815213 / 4000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130404738703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_41 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20665567143629 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (565203372823 / 25000000000000 : ℝ))
      (E := (cell12626 ⟨41, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20665567143629 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (565203372823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_42 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82628265412473 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452163492793 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨42, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82628265412473 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452163492793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_43 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (161316964579 / 195312500000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130410756151 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨43, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (161316964579 / 195312500000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130410756151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_44 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20640082475211 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260825517807 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨44, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20640082475211 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260825517807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_45 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82526397492211 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260829479299 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨45, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82526397492211 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260829479299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_46 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82492488609251 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113041675657 / 5000000000000 : ℝ))
      (E := (cell12626 ⟨46, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82492488609251 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113041675657 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_47 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82458603222809 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260837500047 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨47, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82458603222809 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260837500047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_48 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82424741303879 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260841497117 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨48, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82424741303879 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260841497117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_49 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41195451411801 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130422751187 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨49, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41195451411801 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130422751187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_50 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82357087753261 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (70651547301 / 3125000000000 : ℝ))
      (E := (cell12626 ⟨50, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82357087753261 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (70651547301 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_51 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82323296064283 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (226085352849 / 10000000000000 : ℝ))
      (E := (cell12626 ⟨51, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82323296064283 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (226085352849 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_52 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41144763864121 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130428772167 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨52, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41144763864121 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130428772167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_53 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (1645115654337 / 2000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130430749647 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨53, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (1645115654337 / 2000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130430749647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_54 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41111030500981 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452173101681 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨54, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41111030500981 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452173101681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_55 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41094181277787 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130434754701 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨55, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41094181277787 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130434754701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_56 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82154687349823 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452174711589 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨56, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82154687349823 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452174711589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_57 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82121035356983 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452175506433 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨57, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82121035356983 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452175506433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_58 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82087406549467 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260881546451 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨58, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82087406549467 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260881546451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_59 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (82053800899827 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (226088553761 / 10000000000000 : ℝ))
      (E := (cell12626 ⟨59, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (82053800899827 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (226088553761 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12627_40 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (8269629264511 / 10000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565171020271 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨40, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (8269629264511 / 10000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565171020271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_41 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82662266144693 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260688085697 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨41, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82662266144693 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260688085697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_42 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82628263287621 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130346024897 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨42, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82628263287621 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130346024897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_43 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41297142022073 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260696090251 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨43, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41297142022073 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260696090251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_44 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82560328384671 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130350044287 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨44, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82560328384671 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130350044287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_45 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82526396279749 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565176025609 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨45, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82526396279749 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565176025609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_46 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (1031156096251 / 1250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130354035813 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨46, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (1031156096251 / 1250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130354035813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_47 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (1288415665883 / 1562500000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260712112339 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨47, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (1288415665883 / 1562500000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260712112339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_48 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (2060618525001 / 2500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130358052513 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨48, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (2060618525001 / 2500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130358052513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_49 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41195451410901 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452144021319 / 20000000000000 : ℝ))
      (E := (cell12627 ⟨49, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41195451410901 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452144021319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_50 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41178544026543 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452144822971 / 20000000000000 : ℝ))
      (E := (cell12627 ⟨50, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41178544026543 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452144822971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_51 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41161648332659 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260728127407 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨51, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41161648332659 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260728127407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_52 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (10286191078759 / 12500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260732082613 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨52, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (10286191078759 / 12500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260732082613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_53 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41127891959531 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (226073609567 / 10000000000000 : ℝ))
      (E := (cell12627 ⟨53, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41127891959531 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (226073609567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_54 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (5138878906509 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452148020909 / 20000000000000 : ℝ))
      (E := (cell12627 ⟨54, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (5138878906509 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452148020909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_55 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82188364357313 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260744105993 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨55, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82188364357313 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260744105993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_56 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (20538672362677 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260748096559 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨56, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (20538672362677 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260748096559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_57 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82121037756603 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565188032931 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨57, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82121037756603 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565188032931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_58 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (82087409247413 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260756148523 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨58, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (82087409247413 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260756148523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_59 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (10256725486961 / 12500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130380071441 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨59, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (10256725486961 / 12500000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130380071441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12628_40 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82696289910787 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130279340761 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨40, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82696289910787 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130279340761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_41 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41331131857863 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130281338449 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨41, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41331131857863 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130281338449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_42 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82628261163587 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452113338249 / 20000000000000 : ℝ))
      (E := (cell12628 ⟨42, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82628261163587 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452113338249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_43 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (5162142639039 / 6250000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452114144777 / 20000000000000 : ℝ))
      (E := (cell12628 ⟨43, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (5162142639039 / 6250000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452114144777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_44 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41280163434621 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130287357543 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨44, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41280163434621 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130287357543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_45 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82526395067993 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130289361261 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨45, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82526395067993 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130289361261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_46 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82492486791579 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260582685981 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨46, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82492486791579 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260582685981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_47 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (2576831312839 / 3125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260586721657 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨47, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (2576831312839 / 3125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260586721657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_48 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16484948139359 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226059071 / 10000000000 : ℝ))
      (E := (cell12628 ⟨48, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16484948139359 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226059071 / 10000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_49 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41195451410281 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565148676979 / 25000000000000 : ℝ))
      (E := (cell12628 ⟨49, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41195451410281 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565148676979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_50 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82357088353433 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260598713217 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨50, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82357088353433 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260598713217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_51 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41161648633419 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260602723501 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨51, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41161648633419 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260602723501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_52 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82289529532351 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260606736151 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨52, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82289529532351 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260606736151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_53 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82255785121687 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260610748343 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨53, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82255785121687 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260610748343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_54 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82222064006701 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260614757043 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨54, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82222064006701 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260614757043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_55 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82188366159391 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565154689751 / 25000000000000 : ℝ))
      (E := (cell12628 ⟨55, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82188366159391 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565154689751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_56 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16430938310379 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260622750771 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨56, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16430938310379 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260622750771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_57 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (82121040156489 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260626728683 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨57, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (82121040156489 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260626728683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_58 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (20521852986397 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260630748033 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨58, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (20521852986397 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260630748033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_59 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41026903445871 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226063474563 / 10000000000000 : ℝ))
      (E := (cell12628 ⟨59, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41026903445871 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226063474563 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12629_40 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20674071794339 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130216668731 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨40, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20674071794339 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130216668731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_41 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20665565321903 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452087464733 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨41, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20665565321903 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452087464733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_42 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82628259040369 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (17659697887 / 781250000000 : ℝ))
      (E := (cell12629 ⟨42, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82628259040369 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (17659697887 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_43 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41297140202941 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452089070879 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨43, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41297140202941 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452089070879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_44 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20640081338639 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (141278083657 / 6250000000000 : ℝ))
      (E := (cell12629 ⟨44, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20640081338639 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (141278083657 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_45 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82526393856943 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (56511333489 / 2500000000000 : ℝ))
      (E := (cell12629 ⟨45, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82526393856943 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (56511333489 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_46 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82492485883747 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260457356207 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨46, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82492485883747 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260457356207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_47 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (10307325175727 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130230693453 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨47, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (10307325175727 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130230693453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_48 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41212370197073 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260465370967 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨48, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41212370197073 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260465370967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_49 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82390902819879 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260469365293 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨49, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82390902819879 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260469365293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_50 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41178544327151 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452094673539 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨50, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41178544327151 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452094673539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_51 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20580824467211 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226047737577 / 10000000000000 : ℝ))
      (E := (cell12629 ⟨51, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20580824467211 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226047737577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_52 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82289530435079 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (282560173363 / 12500000000000 : ℝ))
      (E := (cell12629 ⟨52, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82289530435079 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (282560173363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_53 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82255786324723 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226048539827 / 10000000000000 : ℝ))
      (E := (cell12629 ⟨53, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82255786324723 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226048539827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_54 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82222065509633 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260489406831 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨54, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82222065509633 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260489406831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_55 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (5136772997613 / 6250000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130246704671 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨55, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (5136772997613 / 6250000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130246704671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_56 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (16430938730677 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565124350587 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨56, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (16430938730677 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565124350587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_57 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41060521278321 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565125360331 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨57, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41060521278321 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565125360331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_58 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82087414643993 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130252702073 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨58, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82087414643993 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130252702073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_59 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (82053809887991 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (28256367563 / 1250000000000 : ℝ))
      (E := (cell12629 ⟨59, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (82053809887991 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (28256367563 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12630_40 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16539256888963 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452061609781 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨40, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16539256888963 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452061609781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_41 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (1291597794693 / 1562500000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452062405199 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨41, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (1291597794693 / 1562500000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452062405199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_42 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82628256917969 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130158041119 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨42, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82628256917969 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130158041119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_43 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (1032428482349 / 1250000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141270002537 / 6250000000000 : ℝ))
      (E := (cell12630 ⟨43, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (1032428482349 / 1250000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141270002537 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_44 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20640080960153 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130162038261 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨44, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20640080960153 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130162038261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_45 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82526392646599 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130164035633 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨45, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82526392646599 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130164035633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_46 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82492484976583 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452066416461 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨46, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82492484976583 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452066416461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_47 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16491720160283 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (70635501537 / 3125000000000 : ℝ))
      (E := (cell12630 ⟨47, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16491720160283 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (70635501537 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_48 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20606185023023 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (282542510991 / 12500000000000 : ℝ))
      (E := (cell12630 ⟨48, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20606185023023 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (282542510991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_49 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16478180563951 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (90413763149 / 4000000000000 : ℝ))
      (E := (cell12630 ⟨49, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16478180563951 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (90413763149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_50 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20589272238923 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260348078289 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨50, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20589272238923 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260348078289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_51 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41161649235667 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130176042109 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨51, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41161649235667 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130176042109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_52 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41144765669127 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (282544511737 / 12500000000000 : ℝ))
      (E := (cell12630 ⟨52, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41144765669127 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (282544511737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_53 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82255787528171 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452072020899 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨53, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82255787528171 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452072020899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_54 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82222067012941 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260364112979 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨54, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82222067012941 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260364112979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_55 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20547092441141 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260368116101 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨55, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20547092441141 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260368116101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_56 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41077347877589 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452074422081 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨56, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41077347877589 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452074422081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_57 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (4106052247853 / 5000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260376092229 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨57, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (4106052247853 / 5000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260376092229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_58 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (82087417342627 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260380116863 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨58, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (82087417342627 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260380116863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_59 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (5128363305277 / 6250000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452076824223 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨59, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (5128363305277 / 6250000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452076824223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12631_40 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41348140856583 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260182815851 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨40, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41348140856583 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260182815851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_41 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41331128216973 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260186783891 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨41, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41331128216973 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260186783891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_42 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (16525650959277 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260190772993 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨42, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (16525650959277 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260190772993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_43 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41297138385369 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130097391239 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨43, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41297138385369 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130097391239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_44 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82560322327411 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260198811447 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨44, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82560322327411 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260198811447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_45 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (515789946481 / 625000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130101399963 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨45, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (515789946481 / 625000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130101399963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_46 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (10311560508761 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130103402697 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨46, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (10311560508761 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130103402697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_47 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82458600197647 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260210826301 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨47, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82458600197647 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260210826301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_48 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82424739790633 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452042960391 / 20000000000000 : ℝ))
      (E := (cell12631 ⟨48, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82424739790633 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452042960391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_49 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82390902820189 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260218848213 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨49, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82390902820189 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260218848213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_50 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20589272314401 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260222845001 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨50, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20589272314401 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260222845001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_51 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20580824768577 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452045369769 / 20000000000000 : ℝ))
      (E := (cell12631 ⟨51, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20580824768577 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452045369769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_52 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41144766120939 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (282528857141 / 12500000000000 : ℝ))
      (E := (cell12631 ⟨52, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41144766120939 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (282528857141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_53 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (8225578873203 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130117433511 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨53, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (8225578873203 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130117433511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_54 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (5138879282289 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260238816419 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨54, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (5138879282289 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260238816419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_55 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41094185783829 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260242820189 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨55, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41094185783829 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260242820189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_56 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (10269337232159 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260246874947 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨56, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (10269337232159 / 12500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260246874947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_57 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (5132565459859 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260250858817 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨57, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (5132565459859 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260250858817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_58 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (82087420041491 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452050977237 / 20000000000000 : ℝ))
      (E := (cell12631 ⟨58, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (82087420041491 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452050977237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_59 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20513453970267 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130129446927 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨59, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20513453970267 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130129446927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12632_40 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82696278982407 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260057579561 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨40, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82696278982407 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260057579561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_41 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41331127004197 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282507699669 / 12500000000000 : ℝ))
      (E := (cell12632 ⟨41, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41331127004197 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282507699669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_42 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82628252675617 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130032789081 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨42, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82628252675617 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130032789081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_43 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41297137477167 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (565017395013 / 25000000000000 : ℝ))
      (E := (cell12632 ⟨43, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41297137477167 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (565017395013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_44 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (10320040101869 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130036801061 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨44, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (10320040101869 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130036801061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_45 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41263195114013 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260077584397 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨45, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41263195114013 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260077584397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_46 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41246241582131 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130040792177 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨46, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41246241582131 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130040792177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_47 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (8245859959451 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452017120089 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨47, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (8245859959451 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452017120089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_48 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (10303092436221 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260089571977 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨48, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (10303092436221 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260089571977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_49 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82390902821181 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452018722961 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨49, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82390902821181 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452018722961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_50 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (20589272390009 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452019521771 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨50, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (20589272390009 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452019521771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_51 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82323299677767 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260101610651 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨51, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82323299677767 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260101610651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_52 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (1645790662919 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (90404224703 / 4000000000000 : ℝ))
      (E := (cell12632 ⟨52, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (1645790662919 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (90404224703 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_53 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (82255789936301 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130054813401 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨53, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (82255789936301 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130054813401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_54 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41111035010341 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260113635289 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨54, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41111035010341 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260113635289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_55 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (8218837337109 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130058819897 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨55, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (8218837337109 / 10000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130058819897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_56 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (20538674989917 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130060818427 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨56, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (20538674989917 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1130060818427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_57 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41060524879347 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282515702851 / 12500000000000 : ℝ))
      (E := (cell12632 ⟨57, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41060524879347 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282515702851 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_58 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16417484548117 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452025930589 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨58, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16417484548117 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (452025930589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_59 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (10256727359737 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260133664071 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨59, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (10256727359737 / 12500000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2260133664071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12633_40 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82696276252539 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259932398777 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨40, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82696276252539 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259932398777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_41 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41331125791847 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129968203809 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨41, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41331125791847 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129968203809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_42 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16525650111133 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129970190087 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨42, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16525650111133 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129970190087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_43 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (8259427313871 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129972187253 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨43, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (8259427313871 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129972187253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_44 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16512063860647 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451989677943 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨44, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16512063860647 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451989677943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_45 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41263194509899 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259952424681 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨45, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41263194509899 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259952424681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_46 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82492482259103 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259956419191 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨46, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82492482259103 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259956419191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_47 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (20614649748001 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259960430527 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨47, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (20614649748001 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259960430527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_48 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41212369594749 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129982198999 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨48, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41212369594749 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129982198999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_49 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (8239090282273 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (141248027341 / 6250000000000 : ℝ))
      (E := (cell12633 ⟨49, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (8239090282273 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (141248027341 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_50 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (8235708986299 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564993107207 / 25000000000000 : ℝ))
      (E := (cell12633 ⟨50, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (8235708986299 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564993107207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_51 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82323300281711 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259976428637 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨51, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82323300281711 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259976428637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_52 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82289534050469 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129990217133 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨52, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82289534050469 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129990217133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_53 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82255791140983 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451996888577 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨53, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82255791140983 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451996888577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_54 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41111035762557 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451997690291 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨54, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41111035762557 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451997690291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_55 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82188375174861 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259992456729 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨55, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82188375174861 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259992456729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_56 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82154702062367 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259996455247 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨56, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82154702062367 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259996455247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_57 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82121052159909 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1130000221673 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨57, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82121052159909 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1130000221673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_58 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (20521856359977 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1130002238157 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨58, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (20521856359977 / 25000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1130002238157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_59 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (82053821874917 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2260008490957 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨59, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (82053821874917 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2260008490957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12634_40 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82696273523561 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259807214757 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨40, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82696273523561 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259807214757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_41 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (10332781144981 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451962242937 / 20000000000000 : ℝ))
      (E := (cell12634 ⟨41, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (10332781144981 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451962242937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_42 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (8262824843653 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259815237813 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨42, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (8262824843653 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259815237813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_43 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (10324283915483 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259819224651 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨43, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (10324283915483 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259819224651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_44 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (4128015889613 / 5000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259823233059 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨44, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (4128015889613 / 5000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259823233059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_45 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41263193906137 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259827261921 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨45, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41263193906137 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259827261921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_46 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82492481354613 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259831251019 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨46, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82492481354613 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259831251019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_47 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82458598390129 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259835257639 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨47, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82458598390129 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259835257639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_48 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41212369444911 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451967856003 / 20000000000000 : ℝ))
      (E := (cell12634 ⟨48, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41212369444911 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451967856003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_49 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82390902824837 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564960814303 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨49, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82390902824837 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564960814303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_50 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (16471418033293 / 20000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (56496182623 / 2500000000000 : ℝ))
      (E := (cell12634 ⟨50, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (16471418033293 / 20000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (56496182623 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_51 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82323300886139 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259851302803 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨51, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82323300886139 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259851302803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_52 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20572383738859 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259855307197 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨52, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20572383738859 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259855307197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_53 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82255792346077 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259859315269 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨53, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82255792346077 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259859315269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_54 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82222073029921 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259863264913 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨54, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82222073029921 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259863264913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_55 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (8218837697897 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129933635497 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨55, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (8218837697897 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129933635497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_56 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82154704165367 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564967832531 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨56, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82154704165367 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564967832531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_57 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (8212105456139 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564968830107 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨57, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (8212105456139 / 10000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564968830107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_58 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (4104371406973 / 5000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564969824281 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨58, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (4104371406973 / 5000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564969824281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_59 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (82053824872131 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (56497082883 / 2500000000000 : ℝ))
      (E := (cell12634 ⟨59, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (82053824872131 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (56497082883 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12635_40 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (5168516924717 / 6250000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259682144989 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨40, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (5168516924717 / 6250000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259682144989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_41 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41331123368427 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (282460767011 / 12500000000000 : ℝ))
      (E := (cell12635 ⟨41, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41331123368427 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (282460767011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_42 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (8262824631821 / 10000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451938030217 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨42, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (8262824631821 / 10000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451938030217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_43 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82594269509797 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (282461766311 / 12500000000000 : ℝ))
      (E := (cell12635 ⟨43, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82594269509797 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (282461766311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_44 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41280158141013 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129849066079 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨44, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41280158141013 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129849066079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_45 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16505277321091 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (70615692343 / 3125000000000 : ℝ))
      (E := (cell12635 ⟨45, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16505277321091 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (70615692343 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_46 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (8249248045079 / 10000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129853069363 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨46, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (8249248045079 / 10000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129853069363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_47 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (20614649447221 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259710140691 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨47, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (20614649447221 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259710140691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_48 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (4121236929537 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259714159103 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨48, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (4121236929537 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259714159103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_49 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82390902827501 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259718191983 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨49, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82390902827501 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259718191983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_50 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (4117854523523 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259722178159 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨50, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (4117854523523 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259722178159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_51 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (1646466029821 / 2000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129863087077 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨51, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (1646466029821 / 2000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129863087077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_52 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (1645790717217 / 2000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259730177349 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨52, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (1645790717217 / 2000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259730177349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_53 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (4112789677579 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129867092457 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨53, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (4112789677579 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129867092457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_54 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41111037267551 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259738193807 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨54, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41111037267551 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259738193807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_55 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82188378783417 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (112987110039 / 5000000000000 : ℝ))
      (E := (cell12635 ⟨55, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82188378783417 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (112987110039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_56 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (20538676567167 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259746202373 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨56, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (20538676567167 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259746202373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_57 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (1283141515049 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259750194919 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨57, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (1283141515049 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259750194919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_58 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82087430839241 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259754233707 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨58, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82087430839241 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259754233707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_59 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (82053827869539 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259758196353 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨59, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (82053827869539 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259758196353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12636_40 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41348134034137 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129778535993 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨40, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41348134034137 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129778535993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_41 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82662244314713 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451912210859 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨41, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82662244314713 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451912210859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_42 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16525648840141 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (5648912653 / 250000000000 : ℝ))
      (E := (cell12636 ⟨42, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16525648840141 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (5648912653 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_43 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (20648566924127 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129784546009 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨43, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (20648566924127 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129784546009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_44 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41280157386267 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (225957308701 / 10000000000000 : ℝ))
      (E := (cell12636 ⟨44, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41280157386267 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (225957308701 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_45 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (4126319269967 / 5000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259577103847 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨45, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (4126319269967 / 5000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259577103847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_46 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41246239773817 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259581082309 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨46, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41246239773817 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259581082309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_47 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82458597188271 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259585079679 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨47, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82458597188271 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259585079679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_48 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82424738292251 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (225958909419 / 10000000000000 : ℝ))
      (E := (cell12636 ⟨48, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82424738292251 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (225958909419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_49 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41195451415361 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259593123861 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨49, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41195451415361 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259593123861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_50 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (3294283630999 / 4000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259597107519 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨50, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (3294283630999 / 4000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259597107519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_51 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41161651048223 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129800550843 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨51, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41161651048223 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129800550843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_52 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (10286192095839 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (17653164873 / 781250000000 : ℝ))
      (E := (cell12636 ⟨52, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (10286192095839 / 12500000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (17653164873 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_53 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16451158951499 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259609110861 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨53, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16451158951499 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259609110861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_54 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82222076040657 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564903279999 / 25000000000000 : ℝ))
      (E := (cell12636 ⟨54, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82222076040657 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564903279999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_55 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41094190294101 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259617127897 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨55, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41094190294101 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259617127897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_56 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82154708372271 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259621131107 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨56, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82154708372271 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259621131107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_57 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82121059365147 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564906281489 / 25000000000000 : ℝ))
      (E := (cell12636 ⟨57, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82121059365147 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564906281489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_58 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (82087433539251 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129814583867 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨58, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (82087433539251 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129814583867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_59 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41026915433569 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451926626811 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨59, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41026915433569 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451926626811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12637_40 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20674066335491 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451886410899 / 20000000000000 : ℝ))
      (E := (cell12637 ⟨40, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20674066335491 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451886410899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_41 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (5166390118339 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (90377441123 / 4000000000000 : ℝ))
      (E := (cell12637 ⟨41, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (5166390118339 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (90377441123 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_42 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (16525648416803 / 20000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259440026949 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨42, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (16525648416803 / 20000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259440026949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_43 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41297132941999 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259444050431 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨43, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41297132941999 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259444050431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_44 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41280156631891 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451889607757 / 20000000000000 : ℝ))
      (E := (cell12637 ⟨44, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41280156631891 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451889607757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_45 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82526384193929 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259452049677 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨45, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82526384193929 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259452049677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_46 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41246239322573 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259456081771 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨46, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41246239322573 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259456081771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_47 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82458596588287 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259460074609 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨47, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82458596588287 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259460074609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_48 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82424737994357 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129732042639 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨48, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82424737994357 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129732042639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_49 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (164781805669 / 200000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (141216753303 / 6250000000000 : ℝ))
      (E := (cell12637 ⟨49, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (164781805669 / 200000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (141216753303 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_50 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82357091080011 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129736046501 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨50, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82357091080011 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129736046501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_51 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20580825675581 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564869021351 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨51, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20580825675581 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564869021351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_52 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (4114476883651 / 5000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129740043193 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨52, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (4114476883651 / 5000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129740043193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_53 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (4112789798191 / 5000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564871023279 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨53, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (4112789798191 / 5000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564871023279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_54 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82222077546587 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (282436012819 / 12500000000000 : ℝ))
      (E := (cell12637 ⟨54, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82222077546587 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (282436012819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_55 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20547095598331 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564873027861 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨55, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20547095598331 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564873027861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_56 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (5134669404761 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225949611633 / 10000000000000 : ℝ))
      (E := (cell12637 ⟨56, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (5134669404761 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225949611633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_57 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (320785397529 / 390625000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259500113543 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨57, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (320785397529 / 390625000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259500113543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_58 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82087436239489 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259504099207 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨58, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82087436239489 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259504099207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_59 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (82053833864931 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259508128427 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨59, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (82053833864931 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259508128427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12638_40 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (2584258206767 / 3125000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564826758443 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨40, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (2584258206767 / 3125000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564826758443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_41 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82662239472987 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259311057427 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨41, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82662239472987 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259311057427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_42 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (4131411998407 / 5000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259315048331 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨42, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (4131411998407 / 5000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259315048331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_43 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16518852814453 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112965953227 / 5000000000000 : ℝ))
      (E := (cell12638 ⟨43, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16518852814453 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112965953227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_44 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20640077938943 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451864609263 / 20000000000000 : ℝ))
      (E := (cell12638 ⟨44, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20640077938943 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451864609263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_45 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41263191494611 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90373082053 / 4000000000000 : ℝ))
      (E := (cell12638 ⟨45, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41263191494611 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90373082053 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_46 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20623119435831 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (225933107823 / 10000000000000 : ℝ))
      (E := (cell12638 ⟨46, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20623119435831 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (225933107823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_47 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41229297994467 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564833766643 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨47, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41229297994467 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564833766643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_48 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16484947539411 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (14120869209 / 625000000000 : ℝ))
      (E := (cell12638 ⟨48, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16484947539411 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (14120869209 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_49 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16478180567767 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259343096851 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨49, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16478180567767 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259343096851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_50 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82357091385567 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (141209192227 / 6250000000000 : ℝ))
      (E := (cell12638 ⟨50, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82357091385567 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (141209192227 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_51 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82323303308687 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129675533153 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨51, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82323303308687 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129675533153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_52 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (1285774040309 / 1562500000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (282419383281 / 12500000000000 : ℝ))
      (E := (cell12638 ⟨52, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (1285774040309 / 1562500000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (282419383281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_53 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20563949292639 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259359072629 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨53, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20563949292639 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259359072629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_54 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (8222207905289 / 10000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451872616481 / 20000000000000 : ℝ))
      (E := (cell12638 ⟨54, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (8222207905289 / 10000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451872616481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_55 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (642096751553 / 781250000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564841773081 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨55, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (642096751553 / 781250000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564841773081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_56 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82154712580381 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90374843957 / 4000000000000 : ℝ))
      (E := (cell12638 ⟨56, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82154712580381 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (90374843957 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_57 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16424212833993 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259375098539 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨57, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16424212833993 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259375098539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_58 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (82087438939957 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129689573227 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨58, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (82087438939957 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129689573227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_59 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16410767372583 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259383120283 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨59, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16410767372583 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259383120283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12639_40 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82696259892013 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259182068559 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨40, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82696259892013 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259182068559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_41 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41331118526701 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129593041793 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨41, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41331118526701 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129593041793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_42 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (2065705946327 / 2500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259190125347 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨42, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (2065705946327 / 2500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259190125347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_43 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82594262261309 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259194075533 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨43, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82594262261309 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259194075533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_44 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41280155124251 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259198109603 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨44, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41280155124251 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259198109603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_45 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41263190892609 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259202108791 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨45, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41263190892609 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259202108791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_46 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82492476842169 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259206130569 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨46, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82492476842169 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259206130569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_47 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82458595390211 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564802528619 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨47, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82458595390211 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564802528619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_48 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82424737400347 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129607058801 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨48, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82424737400347 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129607058801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_49 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41195451421863 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564804534491 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨49, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41195451421863 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564804534491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_50 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41178545845821 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564805528597 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨50, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41178545845821 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564805528597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_51 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (20580825978883 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259226103393 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨51, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (20580825978883 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259226103393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_52 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41144769743489 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259230161381 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨52, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41144769743489 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259230161381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_53 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82255798377701 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129617083749 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨53, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82255798377701 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129617083749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_54 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82222080559567 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129619059313 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨54, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82222080559567 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129619059313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_55 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82188386004581 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259242129633 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨55, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82188386004581 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259242129633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_56 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (10269339335611 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259246138009 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨56, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (10269339335611 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259246138009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_57 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82121066572771 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451850028017 / 20000000000000 : ℝ))
      (E := (cell12639 ⟨57, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82121066572771 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451850028017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_58 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (20521860410163 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259254191149 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨58, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (20521860410163 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259254191149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_59 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (82053839861093 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259258168809 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨59, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (82053839861093 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259258168809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12640_40 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (8269625716837 / 10000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129528579431 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨40, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (8269625716837 / 10000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129528579431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_41 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20665558658667 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129530582661 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨41, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20665558658667 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129530582661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_42 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41314117869417 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564766299803 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨42, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41314117869417 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564766299803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_43 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82594260451131 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564767300259 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨43, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82594260451131 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564767300259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_44 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20640077185493 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282384146227 / 12500000000000 : ℝ))
      (E := (cell12640 ⟨44, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20640077185493 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282384146227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_45 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82526380581919 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259077163219 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨45, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82526380581919 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259077163219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_46 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82492475941681 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259081179907 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨46, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82492475941681 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259081179907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_47 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41229297396059 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564771304581 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨47, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41229297396059 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564771304581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_48 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (10303092138029 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225908921777 / 10000000000000 : ℝ))
      (E := (cell12640 ⟨48, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (10303092138029 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225908921777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_49 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41195451424587 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259093235143 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨49, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41195451424587 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259093235143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_50 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82357091998237 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225909720927 / 10000000000000 : ℝ))
      (E := (cell12640 ⟨50, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82357091998237 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225909720927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_51 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82323304522861 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564775299167 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨51, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82323304522861 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564775299167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_52 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41144770197313 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259105194717 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨52, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41144770197313 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259105194717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_53 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82255799585257 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259109200581 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨53, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82255799585257 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259109200581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_54 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41111041033309 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129556605609 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨54, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41111041033309 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129556605609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_55 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (16437677562143 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129558611687 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨55, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (16437677562143 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129558611687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_56 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (16430943357939 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129560616793 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨56, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (16430943357939 / 20000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129560616793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_57 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (82121068975841 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282390654773 / 12500000000000 : ℝ))
      (E := (cell12640 ⟨57, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (82121068975841 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (282390654773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_58 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (10260930542697 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259129233291 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨58, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (10260930542697 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2259129233291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_59 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41026921429731 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225913327401 / 10000000000000 : ℝ))
      (E := (cell12640 ⟨59, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41026921429731 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (225913327401 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12641_40 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16539250889123 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129466152339 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨40, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16539250889123 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129466152339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_41 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16532446443357 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282367037829 / 12500000000000 : ℝ))
      (E := (cell12641 ⟨41, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16532446443357 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282367037829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_42 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41314116812701 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129470164357 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨42, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41314116812701 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129470164357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_43 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (8259425864173 / 10000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (70592010107 / 3125000000000 : ℝ))
      (E := (cell12641 ⟨43, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (8259425864173 / 10000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (70592010107 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_44 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41280153618091 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258948285787 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨44, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41280153618091 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258948285787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_45 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41263189689661 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258952332327 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨45, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41263189689661 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258952332327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_46 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (4124623752093 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258956344009 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨46, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (4124623752093 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258956344009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_47 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41229297097327 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282370039901 / 12500000000000 : ℝ))
      (E := (cell12641 ⟨47, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41229297097327 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282370039901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_48 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (8242473680871 / 10000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258964315011 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨48, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (8242473680871 / 10000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258964315011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_49 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82390902855177 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129484164717 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨49, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82390902855177 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129484164717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_50 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (10294636538169 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129486180139 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨50, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (10294636538169 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129486180139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_51 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (5145206570667 / 6250000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258976346131 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨51, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (5145206570667 / 6250000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258976346131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_52 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82289541302721 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258980343323 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨52, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82289541302721 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258980343323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_53 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41127900396611 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258984349021 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨53, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41127900396611 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258984349021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_54 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41111041787021 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258988360179 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨54, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41111041787021 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258988360179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_55 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82188389617187 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282374046693 / 12500000000000 : ℝ))
      (E := (cell12641 ⟨55, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82188389617187 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (282374046693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_56 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82154718894803 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258996385653 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨56, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82154718894803 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258996385653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_57 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (10265133922397 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (451800078567 / 20000000000000 : ℝ))
      (E := (cell12641 ⟨57, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (10265133922397 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (451800078567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_58 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82087447042729 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (225900439121 / 10000000000000 : ℝ))
      (E := (cell12641 ⟨58, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82087447042729 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (225900439121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_59 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (82053845858023 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (451801675339 / 20000000000000 : ℝ))
      (E := (cell12641 ⟨59, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (82053845858023 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (451801675339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12642_40 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82696251723749 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258807447267 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨40, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82696251723749 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258807447267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_41 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82662229799753 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129405718377 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨41, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82662229799753 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129405718377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_42 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (5164264469549 / 6250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451763091013 / 20000000000000 : ℝ))
      (E := (cell12642 ⟨42, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (5164264469549 / 6250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451763091013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_43 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41297128416553 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (22588194427 / 1000000000000 : ℝ))
      (E := (cell12642 ⟨43, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41297128416553 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (22588194427 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_44 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20640076432783 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (28235293219 / 1250000000000 : ℝ))
      (E := (cell12642 ⟨44, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20640076432783 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (28235293219 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_45 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20631594544357 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129413749199 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨45, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20631594544357 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129413749199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_46 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (5155779633919 / 6250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258831505113 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨46, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (5155779633919 / 6250000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258831505113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_47 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82458593597819 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129417738019 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨47, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82458593597819 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129417738019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_48 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (4121236825689 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258839468259 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨48, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (4121236825689 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258839468259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_49 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82390902861737 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (141177717487 / 6250000000000 : ℝ))
      (E := (cell12642 ⟨49, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82390902861737 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (141177717487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_50 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (16471418522597 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129423754219 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨50, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (16471418522597 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129423754219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_51 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41161652869483 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129425746391 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨51, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41161652869483 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129425746391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_52 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41144771105631 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564713872289 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨52, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41144771105631 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564713872289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_53 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82255802001597 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (90354379789 / 4000000000000 : ℝ))
      (E := (cell12642 ⟨53, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82255802001597 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (90354379789 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_54 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82222085081839 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129431753221 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨54, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82222085081839 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129431753221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_55 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (16437678284799 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129433760527 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨55, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (16437678284799 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129433760527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_56 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82154721000211 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258871535097 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨56, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82154721000211 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258871535097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_57 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (3284842951311 / 4000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129437772449 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨57, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (3284842951311 / 4000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129437772449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_58 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82087449744109 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (112943977329 / 5000000000000 : ℝ))
      (E := (cell12642 ⟨58, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82087449744109 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (112943977329 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_59 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (82053848856777 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451776707211 / 20000000000000 : ℝ))
      (E := (cell12642 ⟨59, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (82053848856777 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (451776707211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12643_40 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (8269624900277 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258682645373 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨40, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (8269624900277 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258682645373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_41 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20665556845893 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129343342609 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨41, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20665556845893 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129343342609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_42 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (4131411470049 / 5000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129345318527 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨42, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (4131411470049 / 5000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129345318527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_43 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41297127512629 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258694676489 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨43, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41297127512629 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258694676489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_44 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41280152113411 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129349342507 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨44, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41280152113411 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129349342507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_45 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82526376976237 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258702661433 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨45, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82526376976237 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258702661433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_46 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41246236622107 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258706663219 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨46, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41246236622107 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258706663219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_47 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41229296500807 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258710688813 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨47, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41229296500807 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258710688813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_48 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41212368109721 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451742935503 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨48, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41212368109721 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451742935503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_49 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20597725717213 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129359343109 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨49, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20597725717213 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129359343109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_50 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41178546460569 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129361356363 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨50, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41178546460569 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129361356363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_51 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82323306347743 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258726695623 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨51, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82323306347743 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258726695623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_52 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82289543120249 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258730691239 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨52, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82289543120249 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258730691239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_53 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41127901605191 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258734696739 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨53, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41127901605191 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258734696739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_54 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (8222208659001 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564684677269 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨54, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (8222208659001 / 10000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564684677269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_55 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (4109419661557 / 5000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564685681249 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨55, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (4109419661557 / 5000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564685681249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_56 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (82154723105921 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258746741033 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨56, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (82154723105921 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258746741033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_57 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41060538093319 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564687688379 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨57, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41060538093319 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564687688379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_58 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41043726222859 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564688689641 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨58, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41043726222859 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564688689641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_59 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41026925927861 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258758752091 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨59, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41026925927861 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258758752091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12644_40 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82696246282679 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451711579799 / 20000000000000 : ℝ))
      (E := (cell12644 ⟨40, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82696246282679 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451711579799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_41 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82662224968241 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (225856187173 / 10000000000000 : ℝ))
      (E := (cell12644 ⟨41, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82662224968241 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (225856187173 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_42 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82628227289989 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258565874683 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨42, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82628227289989 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258565874683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_43 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82594253218187 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129284953583 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨43, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82594253218187 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129284953583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_44 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20640075680813 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258573909433 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨44, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20640075680813 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258573909433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_45 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20631593943937 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258577880291 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨45, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20631593943937 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258577880291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_46 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (8249247234639 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258581936091 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨46, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (8249247234639 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258581936091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_47 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82458592406037 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564646474657 / 25000000000000 : ℝ))
      (E := (cell12644 ⟨47, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82458592406037 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564646474657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_48 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82424735925697 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282323742847 / 12500000000000 : ℝ))
      (E := (cell12644 ⟨48, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82424735925697 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282323742847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_49 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41195451438261 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258593948713 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨49, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41195451438261 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258593948713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_50 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (8235709322981 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129298957083 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨50, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (8235709322981 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129298957083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_51 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41161653478501 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258601954653 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨51, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41161653478501 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258601954653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_52 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82289544029681 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129302974787 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨52, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82289544029681 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129302974787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_53 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (10281975552447 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129304977533 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨53, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (10281975552447 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129304977533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_54 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82222088098553 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564653492021 / 25000000000000 : ℝ))
      (E := (cell12644 ⟨54, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82222088098553 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564653492021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_55 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (82188395038621 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258617926277 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨55, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (82188395038621 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258617926277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_56 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (8215472521193 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129310972173 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨56, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (8215472521193 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129310972173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_57 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16424215718153 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258625959547 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨57, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16424215718153 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258625959547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_58 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41043727573777 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129314983999 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨58, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41043727573777 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129314983999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_59 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41026927427429 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451726793123 / 20000000000000 : ℝ))
      (E := (cell12644 ⟨59, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41026927427429 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451726793123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12645_40 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (3307849742539 / 4000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (141152071837 / 6250000000000 : ℝ))
      (E := (cell12645 ⟨40, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (3307849742539 / 4000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (141152071837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_41 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82662222553761 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129218586293 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨41, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82662222553761 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129218586293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_42 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82628225179811 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258441167953 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨42, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82628225179811 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258441167953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_43 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82594251411891 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129222596773 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨43, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82594251411891 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129222596773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_44 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (4128015061021 / 5000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129224594809 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨44, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (4128015061021 / 5000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129224594809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_45 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41263187287981 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129226577487 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨45, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41263187287981 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129226577487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_46 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82492471449231 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258457205967 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨46, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82492471449231 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258457205967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_47 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82458591811089 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258461164389 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨47, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82458591811089 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258461164389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_48 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (2575772988517 / 3125000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564616301279 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨48, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (2575772988517 / 3125000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564616301279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_49 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20597725721187 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129234604161 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨49, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20597725721187 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129234604161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_50 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82357093539 / 100000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129236615357 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨50, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82357093539 / 100000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129236615357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_51 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41161653783371 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564619302719 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨51, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41161653783371 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564619302719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_52 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82289544939559 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258481205137 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨52, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82289544939559 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258481205137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_53 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82255805629179 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129242605329 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨53, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82255805629179 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129242605329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_54 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82222089607469 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129244612197 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨54, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82222089607469 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129244612197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_55 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82188396846439 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (141155827693 / 6250000000000 : ℝ))
      (E := (cell12645 ⟨55, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82188396846439 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (141155827693 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_56 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82154727318239 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129248602077 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨56, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82154727318239 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129248602077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_57 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82121080995157 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258501222133 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨57, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82121080995157 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258501222133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_58 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41043728924809 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258505234049 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨58, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41043728924809 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258505234049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_59 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (82053857854187 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129254617907 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨59, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (82053857854187 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129254617907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12646_40 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41348120422579 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225830845531 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨40, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41348120422579 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225830845531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_41 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (8266222014013 / 10000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258312470259 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨41, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (8266222014013 / 10000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258312470259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_42 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (16525644614089 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129158229039 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨42, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (16525644614089 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129158229039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_43 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20648562401593 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258320476817 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨43, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20648562401593 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258320476817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_44 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82560299718327 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564581116683 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨44, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82560299718327 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564581116683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_45 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41263186688439 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564582121371 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨45, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41263186688439 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564582121371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_46 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41246235276369 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (141145779553 / 6250000000000 : ℝ))
      (E := (cell12646 ⟨46, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41246235276369 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (141145779553 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_47 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (8245859121677 / 10000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (22583364861 / 1000000000000 : ℝ))
      (E := (cell12646 ⟨47, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (8245859121677 / 10000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (22583364861 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_48 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41212367669991 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258340523467 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨48, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41212367669991 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258340523467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_49 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82390902893529 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564586131001 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨49, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82390902893529 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564586131001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_50 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82357093848709 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7057339017 / 312500000000 : ℝ))
      (E := (cell12646 ⟨50, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82357093848709 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7057339017 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_51 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (16464661635393 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564588130823 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨51, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (16464661635393 / 20000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564588130823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_52 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82289545849883 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129178258477 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨52, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82289545849883 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129178258477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_53 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82255806839191 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129180261283 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨53, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82255806839191 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129180261283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_54 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41111045558379 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (56459113427 / 2500000000000 : ℝ))
      (E := (cell12646 ⟨54, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41111045558379 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (56459113427 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_55 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41094199327297 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (56459213931 / 2500000000000 : ℝ))
      (E := (cell12646 ⟨55, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41094199327297 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (56459213931 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_56 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82154729424849 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258372520459 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨56, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82154729424849 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258372520459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_57 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20530270849953 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129188270639 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨57, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20530270849953 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129188270639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_58 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82087460551909 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258380556719 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨58, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82087460551909 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258380556719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_59 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (82053860853707 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129192281347 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨59, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (82053860853707 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129192281347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12647_40 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82696238127727 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564545954187 / 25000000000000 : ℝ))
      (E := (cell12647 ⟨40, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82696238127727 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (564545954187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_41 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82662217727349 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282273477939 / 12500000000000 : ℝ))
      (E := (cell12647 ⟨41, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82662217727349 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (282273477939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_42 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82628220961893 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258191803843 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨42, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82628220961893 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258191803843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_43 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20648561950407 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (141137238487 / 6250000000000 : ℝ))
      (E := (cell12647 ⟨43, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20648561950407 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (141137238487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_44 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82560298216973 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258199858447 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨44, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82560298216973 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258199858447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_45 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16505274435699 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258203871821 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨45, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16505274435699 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258203871821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_46 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82492469656909 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (4516415709 / 200000000000 : ℝ))
      (E := (cell12647 ⟨46, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82492469656909 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (4516415709 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_47 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41229295311539 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258211863761 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨47, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41229295311539 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258211863761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_48 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20606183762003 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258215838897 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨48, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20606183762003 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258215838897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_49 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16478180580573 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129109918401 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨49, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16478180580573 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129109918401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_50 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (10294636769867 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (90328954211 / 4000000000000 : ℝ))
      (E := (cell12647 ⟨50, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (10294636769867 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (90328954211 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_51 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (8232330878767 / 10000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (22582278919 / 1000000000000 : ℝ))
      (E := (cell12647 ⟨51, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (8232330878767 / 10000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (22582278919 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_52 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20572386690163 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (70569746407 / 3125000000000 : ℝ))
      (E := (cell12647 ⟨52, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20572386690163 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (70569746407 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_53 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20563952012403 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258235890787 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨53, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20563952012403 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258235890787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_54 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (82222092626419 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129119953071 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨54, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (82222092626419 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129119953071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_55 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20547100115771 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258243868733 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨55, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20547100115771 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258243868733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_56 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41077365765879 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258247893261 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨56, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41077365765879 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258247893261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_57 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (8212108580473 / 10000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112912595849 / 5000000000000 : ℝ))
      (E := (cell12647 ⟨57, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (8212108580473 / 10000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112912595849 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_58 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20521865813607 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258255876841 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨58, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20521865813607 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258255876841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_59 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41026931926709 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129129943531 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨59, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41026931926709 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129129943531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12648_40 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82696235411183 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258059233707 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨40, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82696235411183 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258059233707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_41 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82662215315417 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258063232349 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨41, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82662215315417 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258063232349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_42 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (10328527356769 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (451613441051 / 20000000000000 : ℝ))
      (E := (cell12648 ⟨42, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (10328527356769 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (451613441051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_43 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (4129712299883 / 5000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (282258901309 / 12500000000000 : ℝ))
      (E := (cell12648 ⟨43, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (4129712299883 / 5000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (282258901309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_44 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41280148358179 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564518811773 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨44, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41280148358179 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564518811773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_45 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41263185490407 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129039627563 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨45, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41263185490407 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129039627563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_46 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (16498493752349 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129041616579 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨46, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (16498493752349 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129041616579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_47 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (16491718006003 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (35282613101 / 1562500000000 : ℝ))
      (E := (cell12648 ⟨47, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (16491718006003 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (35282613101 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_48 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82424734756633 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258091269269 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨48, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82424734756633 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258091269269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_49 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (16478180582551 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564523816157 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨49, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (16478180582551 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564523816157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_50 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41178547234841 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129049611133 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨50, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41178547234841 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129049611133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_51 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (10290413674857 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129051628851 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨51, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (10290413674857 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129051628851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_52 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41144773835933 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129053625163 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨52, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41144773835933 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129053625163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_53 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82255809260441 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129055628139 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨53, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82255809260441 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1129055628139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_54 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (20555523534113 / 25000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258115272509 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨54, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (20555523534113 / 25000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258115272509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_55 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (8218840227191 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (28226491197 / 1250000000000 : ℝ))
      (E := (cell12648 ⟨55, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (8218840227191 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (28226491197 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_56 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (82154733638967 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258123263443 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨56, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (82154733638967 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258123263443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_57 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (10265136026239 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258127290099 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨57, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (10265136026239 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2258127290099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_58 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (3283498638287 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564532828187 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨58, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (3283498638287 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564532828187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_59 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (2051346671333 / 2500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (141133454257 / 6250000000000 : ℝ))
      (E := (cell12648 ⟨59, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (2051346671333 / 2500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (141133454257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12649_40 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41348116347763 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451586929489 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨40, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41348116347763 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451586929489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_41 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41331106452167 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564484659501 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨41, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41331106452167 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564484659501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_42 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (10328527093403 / 12500000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257942662311 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨42, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (10328527093403 / 12500000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257942662311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_43 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41297122097233 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (112897333043 / 5000000000000 : ℝ))
      (E := (cell12649 ⟨43, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41297122097233 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (112897333043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_44 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (516001845103 / 625000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225795063267 / 10000000000000 : ℝ))
      (E := (cell12649 ⟨44, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (516001845103 / 625000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225795063267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_45 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (16505273956767 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (11289773177 / 500000000000 : ℝ))
      (E := (cell12649 ⟨45, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (16505273956767 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (11289773177 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_46 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41246233933623 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257958667707 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨46, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41246233933623 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257958667707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_47 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (4122929471879 / 5000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257962669119 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨47, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (4122929471879 / 5000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257962669119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_48 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41212367232923 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (70561457431 / 3125000000000 : ℝ))
      (E := (cell12649 ⟨48, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41212367232923 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (70561457431 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_49 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (51494314327 / 62500000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257970689573 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨49, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (51494314327 / 62500000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257970689573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_50 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (16471418956189 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257974645393 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨50, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (16471418956189 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257974645393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_51 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20580827502631 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257978679699 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨51, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20580827502631 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257978679699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_52 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (3291581943341 / 4000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451596534377 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨52, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (3291581943341 / 4000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451596534377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_53 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82255810471679 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128993339043 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨53, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82255810471679 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128993339043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_54 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82222095646857 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451598139051 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨54, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82222095646857 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451598139051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_55 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (5136775255067 / 6250000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225799472013 / 10000000000000 : ℝ))
      (E := (cell12649 ⟨55, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (5136775255067 / 6250000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225799472013 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_56 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (3286189429859 / 4000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128999345063 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨56, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (3286189429859 / 4000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128999345063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_57 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (82121090615357 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2258002719779 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨57, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (82121090615357 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2258002719779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_58 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20521867165037 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451601337389 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨58, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20521867165037 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451601337389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_59 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41026934926707 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2258010705841 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨59, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41026934926707 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2258010705841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

end BstLean.Part268
