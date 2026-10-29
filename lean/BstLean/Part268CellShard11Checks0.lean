import BstLean.Part268CellShard11Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12625_0 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (42038565930467 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260774890929 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨0, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (42038565930467 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260774890929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_1 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (21010533186831 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (113038945989 / 5000000000000 : ℝ))
      (E := (cell12625 ⟨1, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (21010533186831 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (113038945989 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_2 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (84007158602109 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260782917373 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨2, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (84007158602109 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260782917373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_3 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10496526173589 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260786892693 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨3, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10496526173589 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260786892693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_4 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83937285070749 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130395456181 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨4, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83937285070749 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130395456181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_5 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83902385612027 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260794927 / 100000000000 : ℝ))
      (E := (cell12625 ⟨5, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83902385612027 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260794927 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_6 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (2620859718017 / 3125000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (3617278219 / 160000000000 : ℝ))
      (E := (cell12625 ⟨6, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (2620859718017 / 3125000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (3617278219 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_7 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83832661128487 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130401457903 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨7, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83832661128487 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130401457903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_8 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (8379783603223 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (141300431599 / 6250000000000 : ℝ))
      (E := (cell12625 ⟨8, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (8379783603223 / 10000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (141300431599 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_9 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (16752607130467 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130405460801 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨9, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (16752607130467 / 20000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130405460801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_10 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83728259953549 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130407456509 / 50000000000000 : ℝ))
      (E := (cell12625 ⟨10, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83728259953549 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (1130407456509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_11 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41846754450401 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (226081888671 / 10000000000000 : ℝ))
      (E := (cell12625 ⟨11, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41846754450401 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (226081888671 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_12 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83658782459209 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452164581477 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨12, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83658782459209 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452164581477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_13 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41812040297033 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452165384677 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨13, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41812040297033 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452165384677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_14 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (83589403270849 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565207720677 / 25000000000000 : ℝ))
      (E := (cell12625 ⟨14, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (83589403270849 / 100000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565207720677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_15 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41777375227607 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565208726869 / 25000000000000 : ℝ))
      (E := (cell12625 ⟨15, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41777375227607 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565208726869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_16 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (20880030528249 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260838887043 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨16, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (20880030528249 / 25000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260838887043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_17 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41742759105103 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565210721233 / 25000000000000 : ℝ))
      (E := (cell12625 ⟨17, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41742759105103 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (565210721233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_18 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (10431367339129 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452169381259 / 20000000000000 : ℝ))
      (E := (cell12625 ⟨18, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (10431367339129 / 12500000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (452169381259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12625_19 : CellCertificate 12625 (177759550859531 / 2000000000000000 : ℝ) (207965046827097 / 125000000000000000 : ℝ) (336111919114857 / 10000000000000000 : ℝ)
    (cell12625 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · norm_num [cell12625]
  · have h := gap_lower (n := 12625) (a := (41708191793919 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260850897793 / 100000000000000 : ℝ))
      (E := (cell12625 ⟨19, by decide⟩).energy) (xi := (336111919114857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12625 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12625]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12625])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12625) (a := (41708191793919 / 50000000000000 : ℝ)) (b := (163164721269 / 100000000000000 : ℝ)) (q := (2260850897793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12625])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12625]

theorem cert12626_0 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (21019279138089 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260649468923 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨0, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (21019279138089 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260649468923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_1 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (84042117761737 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (70645420609 / 3125000000000 : ℝ))
      (E := (cell12626 ⟨1, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (84042117761737 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (70645420609 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_2 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (5250446496191 / 6250000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (8830693271 / 390625000000 : ℝ))
      (E := (cell12626 ⟨2, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (5250446496191 / 6250000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (8830693271 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_3 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83972195047737 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260661473769 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨3, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83972195047737 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260661473769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_4 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83937271051397 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141291591087 / 6250000000000 : ℝ))
      (E := (cell12626 ⟨4, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83937271051397 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141291591087 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_5 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (16780474382769 / 20000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (282583679589 / 12500000000000 : ℝ))
      (E := (cell12626 ⟨5, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (16780474382769 / 20000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (282583679589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_6 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41933748799539 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260673477883 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨6, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41933748799539 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260673477883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_7 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20958162017821 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130338736499 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨7, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20958162017821 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130338736499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_8 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (2094945582371 / 2500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260681429687 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨8, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (2094945582371 / 2500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260681429687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_9 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20940755808577 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260685471353 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨9, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20940755808577 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260685471353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_10 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41864123927217 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130344715577 / 50000000000000 : ℝ))
      (E := (cell12626 ⟨10, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41864123927217 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (1130344715577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_11 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83693497120153 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260693432011 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨11, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83693497120153 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260693432011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_12 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83658770996577 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260697422539 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨12, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83658770996577 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260697422539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_13 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (16724813889801 / 20000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113035073361 / 5000000000000 : ℝ))
      (E := (cell12626 ⟨13, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (16724813889801 / 20000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113035073361 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_14 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (41794696221457 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260705455991 / 100000000000000 : ℝ))
      (E := (cell12626 ⟨14, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (41794696221457 / 50000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (2260705455991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_15 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (2088868498599 / 2500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113035472641 / 5000000000000 : ℝ))
      (E := (cell12626 ⟨15, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (2088868498599 / 2500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (113035472641 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_16 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83520111917979 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141294591459 / 6250000000000 : ℝ))
      (E := (cell12626 ⟨16, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83520111917979 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141294591459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_17 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (10435688541373 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452143486951 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨17, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (10435688541373 / 12500000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452143486951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_18 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (20862732287291 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452144286071 / 20000000000000 : ℝ))
      (E := (cell12626 ⟨18, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (20862732287291 / 25000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (452144286071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12626_19 : CellCertificate 12626 (444384750024487 / 5000000000000000 : ℝ) (1663588561643849 / 1000000000000000000 : ℝ) (33608464029663 / 1000000000000000 : ℝ)
    (cell12626 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · norm_num [cell12626]
  · have h := gap_lower (n := 12626) (a := (83416374338881 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141295340941 / 6250000000000 : ℝ))
      (E := (cell12626 ⟨19, by decide⟩).energy) (xi := (33608464029663 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12626 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12626]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12626])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12626) (a := (83416374338881 / 100000000000000 : ℝ)) (b := (163151638593 / 100000000000000 : ℝ)) (q := (141295340941 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12626])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12626]

theorem cert12627_0 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (16815420249241 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260524042101 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨0, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (16815420249241 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260524042101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_1 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (42021051389269 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130264026123 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨1, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (42021051389269 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130264026123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_2 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (5250445579897 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565133008161 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨2, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (5250445579897 / 6250000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565133008161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_3 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83972180709073 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260536050149 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨3, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83972180709073 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260536050149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_4 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (20984314258579 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260540055663 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨4, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (20984314258579 / 25000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260540055663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_5 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83902358217893 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260544057649 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨5, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83902358217893 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260544057649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_6 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83867484223803 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130274032159 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨6, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83867484223803 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130274032159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_7 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41916317508117 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260552025657 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨7, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41916317508117 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260552025657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_8 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83797810559563 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565139016319 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨8, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83797810559563 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565139016319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_9 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41881505409177 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565140004163 / 25000000000000 : ℝ))
      (E := (cell12627 ⟨9, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41881505409177 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (565140004163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_10 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (16745647151471 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260564060949 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨10, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (16745647151471 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260564060949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_11 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83693485341499 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260568031 / 100000000000 : ℝ))
      (E := (cell12627 ⟨11, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83693485341499 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260568031 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_12 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83658759535903 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130286024763 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨12, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83658759535903 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130286024763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_13 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83624058305863 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (56514400169 / 2500000000000 : ℝ))
      (E := (cell12627 ⟨13, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83624058305863 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (56514400169 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_14 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41794690808429 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260580025021 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨14, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41794690808429 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260580025021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_15 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83554729434547 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (282573006513 / 12500000000000 : ℝ))
      (E := (cell12627 ⟨15, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83554729434547 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (282573006513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_16 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (16704020344953 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260588035471 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨16, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (16704020344953 / 20000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260588035471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_17 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (41742749226763 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260592038643 / 100000000000000 : ℝ))
      (E := (cell12627 ⟨17, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (41742749226763 / 50000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (2260592038643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_18 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (4172545979351 / 5000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452119201709 / 20000000000000 : ℝ))
      (E := (cell12627 ⟨18, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (4172545979351 / 5000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (452119201709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12627_19 : CellCertificate 12627 (888741250099711 / 10000000000000000 : ℝ) (1663456769555781 / 1000000000000000000 : ℝ) (67211473194847 / 2000000000000000 : ℝ)
    (cell12627 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · norm_num [cell12627]
  · have h := gap_lower (n := 12627) (a := (83416365091611 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130300004131 / 50000000000000 : ℝ))
      (E := (cell12627 ⟨19, by decide⟩).energy) (xi := (67211473194847 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12627 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12627]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12627])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12627) (a := (83416365091611 / 100000000000000 : ℝ)) (b := (10196159877 / 6250000000000 : ℝ)) (q := (1130300004131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12627])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12627]

theorem cert12628_0 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (42038542971241 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260398668267 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨0, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (42038542971241 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260398668267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_1 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (84042087797727 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260402698057 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨1, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (84042087797727 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260402698057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_2 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (84007114619997 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260406641027 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨2, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (84007114619997 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260406641027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_3 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83972166372717 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226041067971 / 10000000000000 : ℝ))
      (E := (cell12628 ⟨3, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83972166372717 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226041067971 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_4 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16787448603901 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260414649281 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨4, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16787448603901 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260414649281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_5 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (20975586131043 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260418673973 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨5, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (20975586131043 / 25000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260418673973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_6 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83867470850719 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (113021132309 / 5000000000000 : ℝ))
      (E := (cell12628 ⟨6, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83867470850719 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (113021132309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_7 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (10479077745417 / 12500000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260426689717 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨7, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (10479077745417 / 12500000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260426689717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_8 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (104747247283 / 125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260430638383 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨8, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (104747247283 / 125000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260430638383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_9 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (3350519936179 / 4000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565108668381 / 25000000000000 : ℝ))
      (E := (cell12628 ⟨9, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (3350519936179 / 4000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565108668381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_10 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83728223662311 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260438686331 / 100000000000000 : ℝ))
      (E := (cell12628 ⟨10, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83728223662311 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (2260438686331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_11 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41846736782421 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565110670919 / 25000000000000 : ℝ))
      (E := (cell12628 ⟨11, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41846736782421 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (565110670919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_12 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (16731749615437 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130223336091 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨12, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (16731749615437 / 20000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130223336091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_13 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41812023582319 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (90418026329 / 4000000000000 : ℝ))
      (E := (cell12628 ⟨13, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41812023582319 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (90418026329 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_14 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41794685396341 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282556830991 / 12500000000000 : ℝ))
      (E := (cell12628 ⟨14, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41794685396341 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282556830991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_15 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (41777359463487 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282557330897 / 12500000000000 : ℝ))
      (E := (cell12628 ⟨15, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (41777359463487 / 50000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (282557330897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_16 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83520091533353 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130231330801 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨16, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83520091533353 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130231330801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_17 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83485488577831 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130233319199 / 50000000000000 : ℝ))
      (E := (cell12628 ⟨17, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83485488577831 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (1130233319199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_18 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83450910026601 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452094128173 / 20000000000000 : ℝ))
      (E := (cell12628 ⟨18, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83450910026601 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (452094128173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12628_19 : CellCertificate 12628 (888713004448837 / 10000000000000000 : ℝ) (1663324998347607 / 1000000000000000000 : ℝ) (168015048073229 / 5000000000000000 : ℝ)
    (cell12628 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · norm_num [cell12628]
  · have h := gap_lower (n := 12628) (a := (83416355846027 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226047467391 / 10000000000000 : ℝ))
      (E := (cell12628 ⟨19, by decide⟩).energy) (xi := (168015048073229 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12628 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12628]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12628])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12628) (a := (83416355846027 / 100000000000000 : ℝ)) (b := (32625095917 / 20000000000000 : ℝ)) (q := (226047467391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12628])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12628]

theorem cert12629_0 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (16815414128237 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260273347423 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨0, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (16815414128237 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260273347423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_1 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (10505259102413 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130138669547 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨1, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (10505259102413 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130138669547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_2 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (84007099963989 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260281302529 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨2, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (84007099963989 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260281302529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_3 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83972152038669 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113014265229 / 5000000000000 : ℝ))
      (E := (cell12629 ⟨3, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83972152038669 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113014265229 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_4 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83937229006963 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260289354041 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨4, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83937229006963 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260289354041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_5 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83902330832681 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260293343607 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨5, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83902330832681 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260293343607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_6 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41933728739913 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130148669679 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨6, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41933728739913 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130148669679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_7 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83832608912589 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130150674623 / 50000000000000 : ℝ))
      (E := (cell12629 ⟨7, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83832608912589 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (1130150674623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_8 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20949446273837 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113015266149 / 5000000000000 : ℝ))
      (E := (cell12629 ⟨8, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20949446273837 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (113015266149 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_9 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20940746498167 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565077331487 / 25000000000000 : ℝ))
      (E := (cell12629 ⟨9, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20940746498167 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (565077331487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_10 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83728211569301 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (282539163413 / 12500000000000 : ℝ))
      (E := (cell12629 ⟨10, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83728211569301 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (282539163413 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_11 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (4184673089509 / 5000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260317331983 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨11, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (4184673089509 / 5000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260317331983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_12 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (10457342077553 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260321290507 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨12, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (10457342077553 / 12500000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260321290507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_13 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (20906009006333 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260325305397 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨13, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (20906009006333 / 25000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260325305397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_14 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (16717871994077 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452065864943 / 20000000000000 : ℝ))
      (E := (cell12629 ⟨14, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (16717871994077 / 20000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (452065864943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_15 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41777354210621 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226033329619 / 10000000000000 : ℝ))
      (E := (cell12629 ⟨15, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41777354210621 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (226033329619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_16 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (41760040671871 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260337341739 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨16, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (41760040671871 / 50000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260337341739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_17 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (834854787039 / 1000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260341292221 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨17, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (834854787039 / 1000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260341292221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_18 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (83450900467907 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260345327317 / 100000000000000 : ℝ))
      (E := (cell12629 ⟨18, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (83450900467907 / 100000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (2260345327317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12629_19 : CellCertificate 12629 (35547390523813 / 400000000000000 : ℝ) (831596624007183 / 500000000000000000 : ℝ) (84000707703021 / 2500000000000000 : ℝ)
    (cell12629 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · norm_num [cell12629]
  · have h := gap_lower (n := 12629) (a := (8341634660213 / 10000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (141271833469 / 6250000000000 : ℝ))
      (E := (cell12629 ⟨19, by decide⟩).energy) (xi := (84000707703021 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12629 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12629]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12629])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12629) (a := (8341634660213 / 10000000000000 : ℝ)) (b := (163112403251 / 100000000000000 : ℝ)) (q := (141271833469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12629])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12629]

theorem cert12630_0 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16815411068463 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260148021767 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨0, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16815411068463 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260148021767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_1 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (84042057843267 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260152033187 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨1, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (84042057843267 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260152033187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_2 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (84007085310329 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565039004287 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨2, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (84007085310329 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565039004287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_3 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83972137706929 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452032008101 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨3, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83972137706929 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452032008101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_4 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83937214996689 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260164054151 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨4, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83937214996689 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260164054151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_5 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83902317143419 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (226016800863 / 10000000000000 : ℝ))
      (E := (cell12630 ⟨5, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83902317143419 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (226016800863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_6 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83867444111123 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130086013983 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨6, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83867444111123 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130086013983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_7 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83832595863993 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130088002123 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨7, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83832595863993 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130088002123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_8 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (10474721545801 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141261250193 / 6250000000000 : ℝ))
      (E := (cell12630 ⟨8, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (10474721545801 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (141261250193 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_9 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (16752594716587 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452036806387 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨9, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (16752594716587 / 20000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452036806387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_10 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20932049869581 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260188039943 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨10, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20932049869581 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260188039943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_11 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (10461681252189 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260192033981 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨11, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (10461681252189 / 12500000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260192033981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_12 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41829362582809 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (35315562823 / 1562500000000 : ℝ))
      (E := (cell12630 ⟨12, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41829362582809 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (35315562823 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_13 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41812012443971 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260200006387 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨13, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41812012443971 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260200006387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_14 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41794674574983 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260203997253 / 100000000000000 : ℝ))
      (E := (cell12630 ⟨14, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41794674574983 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (2260203997253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_15 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83554697917349 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565051999787 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨15, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83554697917349 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565051999787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_16 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (20880017788983 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130106008853 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨16, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (20880017788983 / 25000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130106008853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_17 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83485468831731 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452043200023 / 20000000000000 : ℝ))
      (E := (cell12630 ⟨17, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83485468831731 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (452043200023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_18 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (83450890910937 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565055002419 / 25000000000000 : ℝ))
      (E := (cell12630 ⟨18, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (83450890910937 / 100000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (565055002419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12630_19 : CellCertificate 12630 (888656526038147 / 10000000000000000 : ℝ) (831530759275549 / 500000000000000000 : ℝ) (335975569969899 / 10000000000000000 : ℝ)
    (cell12630 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · norm_num [cell12630]
  · have h := gap_lower (n := 12630) (a := (41708168679959 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130111996523 / 50000000000000 : ℝ))
      (E := (cell12630 ⟨19, by decide⟩).energy) (xi := (335975569969899 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12630 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12630]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12630])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12630) (a := (41708168679959 / 50000000000000 : ℝ)) (b := (16309932903 / 10000000000000 : ℝ)) (q := (1130111996523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12630])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12630]

theorem cert12631_0 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (8407704004587 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260022749103 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨0, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (8407704004587 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260022749103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_1 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (5252627679351 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (141251673771 / 6250000000000 : ℝ))
      (E := (cell12631 ⟨1, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (5252627679351 / 6250000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (141251673771 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_2 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (16801414131803 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260030784889 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨2, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (16801414131803 / 20000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260030784889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_3 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83972123377497 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260034771741 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨3, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83972123377497 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260034771741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_4 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83937200988683 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565009687403 / 25000000000000 : ℝ))
      (E := (cell12631 ⟨4, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83937200988683 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565009687403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_5 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (41951151728193 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452008556977 / 20000000000000 : ℝ))
      (E := (cell12631 ⟨5, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (41951151728193 / 50000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (452008556977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_6 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (8386743074461 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260046769949 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨6, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (8386743074461 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260046769949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_7 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20958145704387 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260050770651 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨7, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20958145704387 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260050770651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_8 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (4189887981979 / 5000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130027368349 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨8, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (4189887981979 / 5000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130027368349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_9 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83762961175273 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (90402349339 / 4000000000000 : ℝ))
      (E := (cell12631 ⟨9, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83762961175273 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (90402349339 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_10 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83728187389381 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565015692043 / 25000000000000 : ℝ))
      (E := (cell12631 ⟨10, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83728187389381 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565015692043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_11 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (2092335956171 / 2500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (226006673161 / 10000000000000 : ℝ))
      (E := (cell12631 ⟨11, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (2092335956171 / 2500000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (226006673161 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_12 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83658713712769 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130035373253 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨12, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83658713712769 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130035373253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_13 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (8362401375247 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565018690299 / 25000000000000 : ℝ))
      (E := (cell12631 ⟨13, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (8362401375247 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (565018690299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_14 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (3343573533257 / 4000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260078781803 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨14, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (3343573533257 / 4000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260078781803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_15 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (81596374429 / 97656250000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260082756051 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨15, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (81596374429 / 97656250000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260082756051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_16 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83520060969923 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260086747681 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨16, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83520060969923 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260086747681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_17 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (20871364740331 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (14125567263 / 625000000000 : ℝ))
      (E := (cell12631 ⟨17, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (20871364740331 / 25000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (14125567263 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_18 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (8345088135569 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260094746171 / 100000000000000 : ℝ))
      (E := (cell12631 ⟨18, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (8345088135569 / 10000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (2260094746171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12631_19 : CellCertificate 12631 (35545131731051 / 400000000000000 : ℝ) (332585961990569 / 200000000000000000 : ℝ) (335948313618689 / 10000000000000000 : ℝ)
    (cell12631 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · norm_num [cell12631]
  · have h := gap_lower (n := 12631) (a := (83416328119391 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130049381517 / 50000000000000 : ℝ))
      (E := (cell12631 ⟨19, by decide⟩).energy) (xi := (335948313618689 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12631 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12631]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12631])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12631) (a := (83416328119391 / 100000000000000 : ℝ)) (b := (163086256921 / 100000000000000 : ℝ)) (q := (1130049381517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12631])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12631]

theorem cert12632_0 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (1681540495037 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282487191179 / 12500000000000 : ℝ))
      (E := (cell12632 ⟨0, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (1681540495037 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282487191179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_1 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (84042027898351 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451980304543 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨1, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (84042027898351 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451980304543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_2 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (1312610250157 / 1562500000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (22599055479 / 1000000000000 : ℝ))
      (E := (cell12632 ⟨2, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (1312610250157 / 1562500000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (22599055479 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_3 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83972109050371 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259909556161 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨3, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83972109050371 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259909556161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_4 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (2623037093217 / 3125000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1129956778109 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨4, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (2623037093217 / 3125000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1129956778109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_5 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (4195114488579 / 5000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259917556533 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨5, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (4195114488579 / 5000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259917556533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_6 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16773483476057 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259921565309 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨6, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16773483476057 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259921565309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_7 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (20958142443313 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259925532529 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨7, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (20958142443313 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259925532529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_8 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41898873457431 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (225992952381 / 10000000000000 : ℝ))
      (E := (cell12632 ⟨8, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41898873457431 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (225992952381 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_9 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (20940737192421 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259933546593 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨9, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (20940737192421 / 25000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259933546593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_10 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83728175302471 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259937550031 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨10, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83728175302471 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259937550031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_11 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (1046167830977 / 1250000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259941540993 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨11, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (1046167830977 / 1250000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259941540993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_12 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41829351130937 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259945526097 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨12, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41829351130937 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259945526097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_13 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83624002618913 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259949511717 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨13, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83624002618913 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259949511717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_14 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41794663757381 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282494195263 / 12500000000000 : ℝ))
      (E := (cell12632 ⟨14, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41794663757381 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (282494195263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_15 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41777338457541 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451991501749 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨15, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41777338457541 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451991501749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_16 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (16704010157143 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259961531663 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨16, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (16704010157143 / 20000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259961531663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_17 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (41742724546339 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451993103983 / 20000000000000 : ℝ))
      (E := (cell12632 ⟨17, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (41742724546339 / 50000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (451993103983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_18 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (83450871802167 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1129984768399 / 50000000000000 : ℝ))
      (E := (cell12632 ⟨18, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (83450871802167 / 100000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (1129984768399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12632_19 : CellCertificate 12632 (888600064808683 / 10000000000000000 : ℝ) (1662798122214649 / 1000000000000000000 : ℝ) (167960530878621 / 5000000000000000 : ℝ)
    (cell12632 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · norm_num [cell12632]
  · have h := gap_lower (n := 12632) (a := (1668326377611 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259973528969 / 100000000000000 : ℝ))
      (E := (cell12632 ⟨19, by decide⟩).energy) (xi := (167960530878621 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12632 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12632]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12632])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12632) (a := (1668326377611 / 2000000000000 : ℝ)) (b := (6522927477 / 4000000000000 : ℝ)) (q := (2259973528969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12632])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12632]

theorem cert12633_0 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16815401892051 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129886181379 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨0, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16815401892051 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129886181379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_1 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (8404201292947 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129888187991 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨1, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (8404201292947 / 10000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129888187991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_2 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (42003520681713 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451956072807 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨2, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (42003520681713 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451956072807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_3 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (5248255920347 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451956867179 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨3, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (5248255920347 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451956867179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_4 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (5246073311217 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259788358179 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨4, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (5246073311217 / 6250000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259788358179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_5 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83902276089003 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129896190747 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨5, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83902276089003 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129896190747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_6 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83867404018149 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129898178051 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨6, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83867404018149 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129898178051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_7 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16766511346221 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (45196006957 / 2000000000000 : ℝ))
      (E := (cell12633 ⟨7, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16766511346221 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (45196006957 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_8 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41898867096127 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259804364429 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨8, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41898867096127 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259804364429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_9 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (16752587273233 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564952088817 / 25000000000000 : ℝ))
      (E := (cell12633 ⟨9, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (16752587273233 / 20000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (564952088817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_10 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (10466020402199 / 12500000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129906163743 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨10, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (10466020402199 / 12500000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129906163743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_11 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (3347736588459 / 4000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225981634601 / 10000000000000 : ℝ))
      (E := (cell12633 ⟨11, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (3347736588459 / 4000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (225981634601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_12 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (83658690812933 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259820359449 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨12, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (83658690812933 / 100000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259820359449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_13 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (10452998935909 / 12500000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282478046771 / 12500000000000 : ℝ))
      (E := (cell12633 ⟨13, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (10452998935909 / 12500000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (282478046771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_14 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (3343572667999 / 4000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259828338161 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨14, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (3343572667999 / 4000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259828338161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_15 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41777333208353 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129916186771 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨15, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41777333208353 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129916186771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_16 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41760020301653 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129918184829 / 50000000000000 : ℝ))
      (E := (cell12633 ⟨16, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41760020301653 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (1129918184829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_17 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41742719612897 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (141240020739 / 6250000000000 : ℝ))
      (E := (cell12633 ⟨17, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41742719612897 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (141240020739 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_18 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (41725431125183 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259844323339 / 100000000000000 : ℝ))
      (E := (cell12633 ⟨18, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (41725431125183 / 50000000000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (2259844323339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12633_19 : CellCertificate 12633 (888571840634343 / 10000000000000000 : ℝ) (415666613832889 / 250000000000000000 : ℝ) (41986726798043 / 1250000000000000 : ℝ)
    (cell12633 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · norm_num [cell12633]
  · have h := gap_lower (n := 12633) (a := (651689919089 / 781250000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451969669821 / 20000000000000 : ℝ))
      (E := (cell12633 ⟨19, by decide⟩).energy) (xi := (41986726798043 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12633 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12633]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12633])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12633) (a := (651689919089 / 781250000000 : ℝ)) (b := (163060119039 / 100000000000000 : ℝ)) (q := (451969669821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12633])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12633]

theorem cert12634_0 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (21019248542771 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129823595637 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨0, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (21019248542771 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129823595637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_1 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (42020998981487 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259651224481 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨1, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (42020998981487 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259651224481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_2 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (21001756679787 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129827616647 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨2, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (21001756679787 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129827616647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_3 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41986040201519 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225965922669 / 10000000000000 : ℝ))
      (E := (cell12634 ⟨3, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41986040201519 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225965922669 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_4 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83937158978267 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259663213389 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨4, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83937158978267 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259663213389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_5 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20975565602163 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (45193344037 / 2000000000000 : ℝ))
      (E := (cell12634 ⟨5, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20975565602163 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (45193344037 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_6 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83867390658201 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129835600137 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨6, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83867390658201 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129835600137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_7 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20958135922777 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225967521661 / 10000000000000 : ℝ))
      (E := (cell12634 ⟨7, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20958135922777 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (225967521661 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_8 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (20949430367939 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129839600281 / 50000000000000 : ℝ))
      (E := (cell12634 ⟨8, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (20949430367939 / 25000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (1129839600281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_9 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83762923964717 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259683217511 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨9, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83762923964717 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259683217511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_10 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41864075567373 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259687216609 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨10, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41864075567373 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259687216609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_11 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41846701473391 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259691204723 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨11, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41846701473391 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259691204723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_12 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83658679365947 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (282461898559 / 12500000000000 : ℝ))
      (E := (cell12634 ⟨12, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83658679365947 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (282461898559 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_13 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83623980357547 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564924808083 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨13, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83623980357547 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564924808083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_14 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (16717861177413 / 20000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259703226233 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨14, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (16717861177413 / 20000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259703226233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_15 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (10444331990021 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564926808533 / 25000000000000 : ℝ))
      (E := (cell12634 ⟨15, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (10444331990021 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (564926808533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_16 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (10440003802837 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451942240697 / 20000000000000 : ℝ))
      (E := (cell12634 ⟨16, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (10440003802837 / 12500000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (451942240697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_17 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (83485429360671 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259715197807 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨17, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (83485429360671 / 100000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259715197807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_18 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (651959786721 / 781250000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259719222241 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨18, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (651959786721 / 781250000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259719222241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12634_19 : CellCertificate 12634 (888543620752229 / 10000000000000000 : ℝ) (166253480929861 / 100000000000000000 : ℝ) (67173314299757 / 2000000000000000 : ℝ)
    (cell12634 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · norm_num [cell12634]
  · have h := gap_lower (n := 12634) (a := (41708150203959 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259723223441 / 100000000000000 : ℝ))
      (E := (cell12634 ⟨19, by decide⟩).energy) (xi := (67173314299757 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12634 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12634]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12634])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12634) (a := (41708150203959 / 50000000000000 : ℝ)) (b := (32609410653 / 20000000000000 : ℝ)) (q := (2259723223441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12634])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12634]

theorem cert12635_0 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16815395776867 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451904426119 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨0, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16815395776867 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451904426119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_1 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (42020991499431 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129763063021 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨1, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (42020991499431 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129763063021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_2 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (2625219127413 / 3125000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564882524457 / 25000000000000 : ℝ))
      (E := (cell12635 ⟨2, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (2625219127413 / 3125000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564882524457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_3 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83972066082829 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129767056401 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨3, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83972066082829 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129767056401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_4 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83937144979327 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451907624371 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨4, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83937144979327 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451907624371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_5 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (2621945272829 / 3125000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564885533361 / 25000000000000 : ℝ))
      (E := (cell12635 ⟨5, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (2621945272829 / 3125000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (564885533361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_6 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (2096684432511 / 2500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259546097827 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨6, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (2096684432511 / 2500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259546097827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_7 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41916265326629 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259550080849 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨7, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41916265326629 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259550080849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_8 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (10474713594171 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129777045101 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨8, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (10474713594171 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129777045101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_9 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (4188145578267 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (225955807531 / 10000000000000 : ℝ))
      (E := (cell12635 ⟨9, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (4188145578267 / 5000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (225955807531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_10 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83728139053931 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (225956210133 / 10000000000000 : ℝ))
      (E := (cell12635 ⟨10, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83728139053931 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (225956210133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_11 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83693391184081 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451913223427 / 20000000000000 : ℝ))
      (E := (cell12635 ⟨11, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83693391184081 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (451913223427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_12 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (16731733584183 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129785035629 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨12, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (16731733584183 / 20000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129785035629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_13 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (10452996153717 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129787043107 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨13, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (10452996153717 / 12500000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129787043107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_14 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (1306082735563 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (112978905503 / 5000000000000 : ℝ))
      (E := (cell12635 ⟨14, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (1306082735563 / 1562500000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (112978905503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_15 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (83554645425467 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259582090519 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨15, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (83554645425467 / 100000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259582090519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_16 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (41760010121943 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (90383443653 / 4000000000000 : ℝ))
      (E := (cell12635 ⟨16, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (41760010121943 / 50000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (90383443653 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_17 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (20871354874327 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259590117867 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨17, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (20871354874327 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259590117867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_18 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (20862710787983 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129797058529 / 50000000000000 : ℝ))
      (E := (cell12635 ⟨18, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (20862710787983 / 25000000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (1129797058529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12635_19 : CellCertificate 12635 (222128851290329 / 2500000000000000 : ℝ) (831201592055431 / 500000000000000000 : ℝ) (335839333099353 / 10000000000000000 : ℝ)
    (cell12635 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · norm_num [cell12635]
  · have h := gap_lower (n := 12635) (a := (5213518198383 / 6250000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259598093731 / 100000000000000 : ℝ))
      (E := (cell12635 ⟨19, by decide⟩).energy) (xi := (335839333099353 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12635 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12635]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12635])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12635) (a := (5213518198383 / 6250000000000 : ℝ)) (b := (203792487 / 125000000000 : ℝ)) (q := (2259598093731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12635])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12635]

theorem cert12636_0 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (8407696360001 / 10000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259397065109 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨0, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (8407696360001 / 10000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259397065109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_1 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (84041968037133 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129700511419 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨1, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (84041968037133 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129700511419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_2 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (84006997437627 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (35303203367 / 1562500000000 : ℝ))
      (E := (cell12636 ⟨2, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (84006997437627 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (35303203367 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_3 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (20993012941231 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282426131513 / 12500000000000 : ℝ))
      (E := (cell12636 ⟨3, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (20993012941231 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282426131513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_4 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83937130982653 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564853256419 / 25000000000000 : ℝ))
      (E := (cell12636 ⟨4, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83937130982653 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564853256419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_5 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (8390223505463 / 10000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129708530217 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨5, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (8390223505463 / 10000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129708530217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_6 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41933681972433 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259421048761 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨6, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41933681972433 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259421048761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_7 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (20958129404389 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (4518850113 / 200000000000 : ℝ))
      (E := (cell12636 ⟨7, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (20958129404389 / 25000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (4518850113 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_8 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (2618678001159 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (45188580667 / 2000000000000 : ℝ))
      (E := (cell12636 ⟨8, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (2618678001159 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (45188580667 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_9 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (2617590599001 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282429130587 / 12500000000000 : ℝ))
      (E := (cell12636 ⟨9, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (2617590599001 / 3125000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (282429130587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_10 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83728126975147 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564859259921 / 25000000000000 : ℝ))
      (E := (cell12636 ⟨10, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83728126975147 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (564859259921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_11 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83693379423373 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129720512591 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨11, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83693379423373 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129720512591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_12 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16731731295567 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451889001561 / 20000000000000 : ℝ))
      (E := (cell12636 ⟨12, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16731731295567 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (451889001561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_13 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (522649738149 / 625000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129724526013 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨13, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (522649738149 / 625000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129724526013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_14 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (41794642133437 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (70607907743 / 3125000000000 : ℝ))
      (E := (cell12636 ⟨14, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (41794642133437 / 50000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (70607907743 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_15 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83554634932603 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259457059011 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨15, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83554634932603 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259457059011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_16 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83520010066873 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (112973051659 / 5000000000000 : ℝ))
      (E := (cell12636 ⟨16, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83520010066873 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (112973051659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_17 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (16697081927141 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259465033801 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨17, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (16697081927141 / 20000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259465033801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_18 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83450833605297 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259469007789 / 100000000000000 : ℝ))
      (E := (cell12636 ⟨18, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83450833605297 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (2259469007789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12636_19 : CellCertificate 12636 (888487193860577 / 10000000000000000 : ℝ) (831135789881679 / 500000000000000000 : ℝ) (167906049592419 / 5000000000000000 : ℝ)
    (cell12636 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · norm_num [cell12636]
  · have h := gap_lower (n := 12636) (a := (83416281942021 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129736509111 / 50000000000000 : ℝ))
      (E := (cell12636 ⟨19, by decide⟩).energy) (xi := (167906049592419 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12636 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12636]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12636])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12636) (a := (83416281942021 / 100000000000000 : ℝ)) (b := (81510464023 / 50000000000000 : ℝ)) (q := (1129736509111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12636])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12636]

theorem cert12637_0 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (42038474159053 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259271994821 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨0, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (42038474159053 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259271994821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_1 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (84041953077787 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259276030527 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨1, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (84041953077787 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259276030527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_2 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (84006982800381 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259279986277 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨2, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (84006982800381 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259279986277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_3 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20993009362331 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564820996681 / 25000000000000 : ℝ))
      (E := (cell12637 ⟨3, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20993009362331 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (564820996681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_4 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83937116988243 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129643991377 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨4, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83937116988243 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129643991377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_5 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41951110690479 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (282411497853 / 12500000000000 : ℝ))
      (E := (cell12637 ⟨5, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41951110690479 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (282411497853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_6 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41933675295739 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129647997567 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨6, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41933675295739 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129647997567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_7 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41916252292001 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225930002763 / 10000000000000 : ℝ))
      (E := (cell12637 ⟨7, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41916252292001 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225930002763 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_8 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20949420830729 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225930403001 / 10000000000000 : ℝ))
      (E := (cell12637 ⟨8, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20949420830729 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225930403001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_9 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83762886772793 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129654004821 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨9, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83762886772793 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129654004821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_10 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (10466014362299 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (56482799341 / 2500000000000 : ℝ))
      (E := (cell12637 ⟨10, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (10466014362299 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (56482799341 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_11 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (5230835479041 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225931598693 / 10000000000000 : ℝ))
      (E := (cell12637 ⟨11, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (5230835479041 / 6250000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (225931598693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_12 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20914661259177 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451863999623 / 20000000000000 : ℝ))
      (E := (cell12637 ⟨12, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20914661259177 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (451863999623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_13 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83623946979857 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (56483100339 / 2500000000000 : ℝ))
      (E := (cell12637 ⟨13, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83623946979857 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (56483100339 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_14 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83589273459591 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (361492477 / 16000000000 : ℝ))
      (E := (cell12637 ⟨14, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83589273459591 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (361492477 / 16000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_15 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (10444328055197 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259332023301 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨15, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (10444328055197 / 12500000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259332023301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_16 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83519999891659 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259336029051 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨16, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83519999891659 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259336029051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_17 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (41742699887931 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129670001907 / 50000000000000 : ℝ))
      (E := (cell12637 ⟨17, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (41742699887931 / 50000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (1129670001907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_18 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (83450824060383 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259344010887 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨18, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (83450824060383 / 100000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259344010887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12637_19 : CellCertificate 12637 (444229493424493 / 5000000000000000 : ℝ) (103883749765697 / 62500000000000000 : ℝ) (83946217438507 / 2500000000000000 : ℝ)
    (cell12637 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · norm_num [cell12637]
  · have h := gap_lower (n := 12637) (a := (20854068177899 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259347996919 / 100000000000000 : ℝ))
      (E := (cell12637 ⟨19, by decide⟩).energy) (xi := (83946217438507 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12637 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12637]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12637])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12637) (a := (20854068177899 / 25000000000000 : ℝ)) (b := (815039343 / 500000000000 : ℝ)) (q := (2259347996919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12637])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12637]

theorem cert12638_0 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (2627404157457 / 3125000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259147035339 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨0, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (2627404157457 / 3125000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259147035339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_1 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (84041938120823 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129575516727 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨1, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (84041938120823 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129575516727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_2 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (42003484082739 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564788752549 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨2, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (42003484082739 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564788752549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_3 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83972023136027 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259159032411 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨3, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83972023136027 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259159032411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_4 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83937102996097 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259162993089 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨4, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83937102996097 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259162993089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_5 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (8390220770951 / 10000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451833403291 / 20000000000000 : ℝ))
      (E := (cell12638 ⟨5, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (8390220770951 / 10000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (451833403291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_6 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20966834310069 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259170994891 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨6, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20966834310069 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259170994891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_7 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41916245776297 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (7059921857 / 312500000000 : ℝ))
      (E := (cell12638 ⟨7, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41916245776297 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (7059921857 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_8 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20949417652713 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259179022189 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨8, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20949417652713 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259179022189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_9 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83762874379623 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259183028161 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨9, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83762874379623 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259183028161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_10 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20932025705917 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (225918701927 / 10000000000000 : ℝ))
      (E := (cell12638 ⟨10, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20932025705917 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (225918701927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_11 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83693355907929 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259191002381 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨11, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83693355907929 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259191002381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_12 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83658633597533 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129597492053 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨12, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83658633597533 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129597492053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_13 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (20905983964447 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259199028919 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨13, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (20905983964447 / 25000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259199028919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_14 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83589262654183 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129601513373 / 50000000000000 : ℝ))
      (E := (cell12638 ⟨14, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83589262654183 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (1129601513373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_15 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (16710922790477 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259206983389 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨15, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (16710922790477 / 20000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259206983389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_16 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41759994859121 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (56480275519 / 2500000000000 : ℝ))
      (E := (cell12638 ⟨16, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41759994859121 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (56480275519 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_17 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83485389917777 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564803756977 / 25000000000000 : ℝ))
      (E := (cell12638 ⟨17, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83485389917777 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (564803756977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_18 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (83450814517189 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259219009903 / 100000000000000 : ℝ))
      (E := (cell12638 ⟨18, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (83450814517189 / 100000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (2259219009903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12638_19 : CellCertificate 12638 (11105384801569 / 125000000000000 : ℝ) (831004216784647 / 500000000000000000 : ℝ) (67151528961143 / 2000000000000000 : ℝ)
    (cell12638 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · norm_num [cell12638]
  · have h := gap_lower (n := 12638) (a := (41708131741427 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112961151491 / 5000000000000 : ℝ))
      (E := (cell12638 ⟨19, by decide⟩).energy) (xi := (67151528961143 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12638 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12638]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12638])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12638) (a := (41708131741427 / 50000000000000 : ℝ)) (b := (162994811263 / 100000000000000 : ℝ)) (q := (112961151491 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12638])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12638]

theorem cert12639_0 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (21019229440391 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129511035527 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨0, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (21019229440391 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129511035527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_1 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (525262019789 / 625000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (282378261181 / 12500000000000 : ℝ))
      (E := (cell12639 ⟨1, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (525262019789 / 625000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (282378261181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_2 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (84006953532917 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451806017449 / 20000000000000 : ℝ))
      (E := (cell12639 ⟨2, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (84006953532917 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451806017449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_3 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (10496501103129 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259034073419 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨3, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (10496501103129 / 12500000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259034073419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_4 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (16787417801243 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259038056681 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨4, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (16787417801243 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259038056681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_5 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83902194040287 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129521022743 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨5, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83902194040287 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129521022743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_6 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83867323891259 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259046048033 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨6, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83867323891259 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259046048033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_7 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (20958119630833 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129525036133 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨7, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (20958119630833 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129525036133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_8 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (16759531580179 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259054067879 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨8, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (16759531580179 / 20000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259054067879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_9 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (41881430994261 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (3529778191 / 156250000000 : ℝ))
      (E := (cell12639 ⟨9, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (41881430994261 / 50000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (3529778191 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_10 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83728090750973 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259062060501 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨10, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83728090750973 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259062060501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_11 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83693344153193 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564766517883 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨11, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83693344153193 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564766517883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_12 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (8365862216031 / 10000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451814016389 / 20000000000000 : ℝ))
      (E := (cell12639 ⟨12, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (8365862216031 / 10000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (451814016389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_13 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (2613247648051 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129537019999 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨13, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (2613247648051 / 3125000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129537019999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_14 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83589251850649 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129539034001 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨14, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83589251850649 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129539034001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_15 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (8355460346503 / 10000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129541027793 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨15, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (8355460346503 / 10000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129541027793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_16 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83519979546623 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564771516621 / 25000000000000 : ℝ))
      (E := (cell12639 ⟨16, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83519979546623 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (564771516621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_17 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83485380061451 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129545023939 / 50000000000000 : ℝ))
      (E := (cell12639 ⟨17, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83485380061451 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (1129545023939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_18 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (20862701243929 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259094063061 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨18, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (20862701243929 / 25000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259094063061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12639_19 : CellCertificate 12639 (13881290401393 / 156250000000000 : ℝ) (1661876891712839 / 1000000000000000000 : ℝ) (33573042433869 / 1000000000000000 : ℝ)
    (cell12639 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · norm_num [cell12639]
  · have h := gap_lower (n := 12639) (a := (83416254255793 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259098058679 / 100000000000000 : ℝ))
      (E := (cell12639 ⟨19, by decide⟩).energy) (xi := (33573042433869 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12639 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12639]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12639])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12639) (a := (83416254255793 / 100000000000000 : ℝ)) (b := (32596351207 / 20000000000000 : ℝ)) (q := (2259098058679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12639])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12639]

theorem cert12640_0 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (84076902486923 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (70590536243 / 3125000000000 : ℝ))
      (E := (cell12640 ⟨0, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (84076902486923 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (70590536243 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_1 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (42020954107019 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564725285171 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨1, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (42020954107019 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564725285171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_2 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (42003469451349 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258905159577 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨2, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (42003469451349 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258905159577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_3 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83971994516341 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258909167623 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨3, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83971994516341 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258909167623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_4 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20984268754649 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564728278909 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨4, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20984268754649 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564728278909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_5 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (10487772546661 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129458563921 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨5, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (10487772546661 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129458563921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_6 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83867310544427 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564730288641 / 25000000000000 : ℝ))
      (E := (cell12640 ⟨6, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83867310544427 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (564730288641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_7 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (10479058187027 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (90357005831 / 4000000000000 : ℝ))
      (E := (cell12640 ⟨7, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (10479058187027 / 12500000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (90357005831 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_8 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20949411298261 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129464583543 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨8, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20949411298261 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129464583543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_9 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20449914453 / 24414062500 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129466583957 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨9, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20449914453 / 24414062500 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129466583957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_10 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83728078680307 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129468577687 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨10, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83728078680307 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129468577687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_11 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (1307708318757 / 1562500000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129470568163 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨11, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (1307708318757 / 1562500000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129470568163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_12 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41829305362519 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258945117383 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨12, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41829305362519 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258945117383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_13 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (20905978404847 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129474581509 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨13, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (20905978404847 / 25000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129474581509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_14 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83589241048989 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141184572697 / 6250000000000 : ℝ))
      (E := (cell12640 ⟨14, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83589241048989 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (141184572697 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_15 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (8355459297951 / 10000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (451791424717 / 20000000000000 : ℝ))
      (E := (cell12640 ⟨15, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (8355459297951 / 10000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (451791424717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_16 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (104399961721 / 125000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258961166231 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨16, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (104399961721 / 125000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258961166231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_17 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83485370206883 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258965121933 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨17, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83485370206883 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258965121933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_18 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (83450795435963 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258969112139 / 100000000000000 : ℝ))
      (E := (cell12640 ⟨18, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (83450795435963 / 100000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (2258969112139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12640_19 : CellCertificate 12640 (44418719576943 / 500000000000000 : ℝ) (1661745370676843 / 1000000000000000000 : ℝ) (163917582203 / 4882812500000 : ℝ)
    (cell12640 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · norm_num [cell12640]
  · have h := gap_lower (n := 12640) (a := (41708122515207 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129486570873 / 50000000000000 : ℝ))
      (E := (cell12640 ⟨19, by decide⟩).energy) (xi := (163917582203 / 4882812500000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12640 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12640]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12640])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12640) (a := (41708122515207 / 50000000000000 : ℝ)) (b := (162968702913 / 100000000000000 : ℝ)) (q := (1129486570873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12640])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12640]

theorem cert12641_0 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (42038443607351 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (22587722437 / 1000000000000 : ℝ))
      (E := (cell12641 ⟨0, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (42038443607351 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (22587722437 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_1 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (84041893264217 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564694061247 / 25000000000000 : ℝ))
      (E := (cell12641 ⟨1, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (84041893264217 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (564694061247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_2 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (4200346213741 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258780285041 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨2, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (4200346213741 / 5000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258780285041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_3 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (1679439604199 / 2000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (45175685143 / 2000000000000 : ℝ))
      (E := (cell12641 ⟨3, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (1679439604199 / 2000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (45175685143 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_4 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (2098426525831 / 2500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258788285749 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨4, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (2098426525831 / 2500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258788285749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_5 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83902166708511 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129396131761 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨5, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83902166708511 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129396131761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_6 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83867297199779 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258796256537 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨6, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83867297199779 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258796256537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_7 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16766490494249 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (70587508523 / 3125000000000 : ℝ))
      (E := (cell12641 ⟨7, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16766490494249 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (70587508523 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_8 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (837976324873 / 1000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129402130907 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨8, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (837976324873 / 1000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129402130907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_9 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83762837212521 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (45176165783 / 2000000000000 : ℝ))
      (E := (cell12641 ⟨9, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83762837212521 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (45176165783 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_10 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83728066611669 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258812245849 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨10, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83728066611669 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258812245849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_11 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83693320649691 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (90352650193 / 4000000000000 : ℝ))
      (E := (cell12641 ⟨11, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83693320649691 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (90352650193 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_12 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83658599291717 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129410132337 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨12, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83658599291717 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129410132337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_13 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83623902503057 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129412140879 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨13, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83623902503057 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129412140879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_14 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (41794615124601 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (141176765879 / 6250000000000 : ℝ))
      (E := (cell12641 ⟨14, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (41794615124601 / 50000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (141176765879 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_15 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (3342183299833 / 4000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258832245541 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨15, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (3342183299833 / 4000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258832245541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_16 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83519959208773 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258836261817 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨16, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83519959208773 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258836261817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_17 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (83485360354073 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258840250069 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨17, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (83485360354073 / 100000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258840250069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_18 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (10431348237241 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258844273589 / 100000000000000 : ℝ))
      (E := (cell12641 ⟨18, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (10431348237241 / 12500000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (2258844273589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12641_19 : CellCertificate 12641 (444173100836809 / 5000000000000000 : ℝ) (1661613870456363 / 1000000000000000000 : ℝ) (335675996843669 / 10000000000000000 : ℝ)
    (cell12641 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · norm_num [cell12641]
  · have h := gap_lower (n := 12641) (a := (16683247161343 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129424139511 / 50000000000000 : ℝ))
      (E := (cell12641 ⟨19, by decide⟩).energy) (xi := (335675996843669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12641 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12641]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12641])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12641) (a := (16683247161343 / 20000000000000 : ℝ)) (b := (162955651899 / 100000000000000 : ℝ)) (q := (1129424139511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12641])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12641]

theorem cert12642_0 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (84076871944901 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129323719217 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨0, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (84076871944901 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129323719217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_1 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (10505234789597 / 12500000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564662850591 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨1, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (10505234789597 / 12500000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564662850591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_2 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (42003454824641 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (225865540579 / 10000000000000 : ℝ))
      (E := (cell12642 ⟨2, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (42003454824641 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (225865540579 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_3 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83971965905861 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564664849969 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨3, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83971965905861 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564664849969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_4 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (16787409410029 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564665862807 / 25000000000000 : ℝ))
      (E := (cell12642 ⟨4, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (16787409410029 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (564665862807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_5 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41951076522979 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (141166715783 / 6250000000000 : ℝ))
      (E := (cell12642 ⟨5, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41951076522979 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (141166715783 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_6 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (16773456771463 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (22586714119 / 1000000000000 : ℝ))
      (E := (cell12642 ⟨6, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (16773456771463 / 20000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (22586714119 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_7 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83832439448419 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129337697591 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨7, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83832439448419 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129337697591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_8 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83797619783661 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (112933970503 / 5000000000000 : ℝ))
      (E := (cell12642 ⟨8, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83797619783661 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (112933970503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_9 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (4188141241381 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (17645964109 / 781250000000 : ℝ))
      (E := (cell12642 ⟨9, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (4188141241381 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (17645964109 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_10 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83728054545059 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129343724003 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨10, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83728054545059 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129343724003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_11 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20923327225231 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (225869142703 / 10000000000000 : ℝ))
      (E := (cell12642 ⟨11, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20923327225231 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (225869142703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_12 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41829293930173 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258695407649 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨12, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41829293930173 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258695407649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_13 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (20905972847159 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (90347975849 / 4000000000000 : ℝ))
      (E := (cell12642 ⟨13, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (20905972847159 / 25000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (90347975849 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_14 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (10448652431411 / 12500000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258703398871 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨14, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (10448652431411 / 12500000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258703398871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_15 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83554572013973 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258707421457 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨15, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83554572013973 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258707421457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_16 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (41759974521271 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129355705713 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨16, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (41759974521271 / 50000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129355705713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_17 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (4174267525151 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258715432291 / 100000000000000 : ℝ))
      (E := (cell12642 ⟨17, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (4174267525151 / 5000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (2258715432291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_18 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83450776361613 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (28233992887 / 1250000000000 : ℝ))
      (E := (cell12642 ⟨18, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83450776361613 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (28233992887 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12642_19 : CellCertificate 12642 (888318016092403 / 10000000000000000 : ℝ) (830741195523229 / 500000000000000000 : ℝ) (167824394906629 / 5000000000000000 : ℝ)
    (cell12642 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · norm_num [cell12642]
  · have h := gap_lower (n := 12642) (a := (83416226584697 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129361706129 / 50000000000000 : ℝ))
      (E := (cell12642 ⟨19, by decide⟩).energy) (xi := (167824394906629 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12642 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12642]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12642])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12642) (a := (83416226584697 / 100000000000000 : ℝ)) (b := (162942602991 / 100000000000000 : ℝ)) (q := (1129361706129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12642])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12642]

theorem cert12643_0 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (42038428338759 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129261314187 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨0, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (42038428338759 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129261314187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_1 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (84041863371713 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129263306407 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨1, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (84041863371713 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129263306407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_2 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (16801379005217 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129265318763 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨2, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (16801379005217 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129265318763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_3 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83971951604073 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258534595801 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨3, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83971951604073 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258534595801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_4 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (327879035427 / 390625000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (282317326509 / 12500000000000 : ℝ))
      (E := (cell12643 ⟨4, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (327879035427 / 390625000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (282317326509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_5 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83902139385627 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (112927131847 / 5000000000000 : ℝ))
      (E := (cell12643 ⟨5, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83902139385627 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (112927131847 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_6 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41933635258517 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258546620653 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨6, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41933635258517 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258546620653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_7 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83832426427737 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (45171012581 / 2000000000000 : ℝ))
      (E := (cell12643 ⟨7, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83832426427737 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (45171012581 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_8 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (5237350442633 / 6250000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258554611823 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨8, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (5237350442633 / 6250000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258554611823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_9 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41881406222393 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258558634349 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨9, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41881406222393 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258558634349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_10 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20932010620119 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258562645769 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨10, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20932010620119 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258562645769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_11 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (16738659430829 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258566594881 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨11, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (16738659430829 / 20000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258566594881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_12 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20914644107731 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451714120879 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨12, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20914644107731 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451714120879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_13 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83623880276127 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258574622633 / 100000000000000 : ℝ))
      (E := (cell12643 ⟨13, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83623880276127 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (2258574622633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_14 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (83589208655247 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (90343143903 / 4000000000000 : ℝ))
      (E := (cell12643 ⟨14, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (83589208655247 / 100000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (90343143903 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_15 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20888640383489 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (282322824147 / 12500000000000 : ℝ))
      (E := (cell12643 ⟨15, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20888640383489 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (282322824147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_16 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (41759969439053 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129293307529 / 50000000000000 : ℝ))
      (E := (cell12643 ⟨16, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (41759969439053 / 50000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (1129293307529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_17 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (20871335163431 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564647652599 / 25000000000000 : ℝ))
      (E := (cell12643 ⟨17, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (20871335163431 / 25000000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (564647652599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_18 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (10431345853377 / 12500000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (28232433031 / 1250000000000 : ℝ))
      (E := (cell12643 ⟨18, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (10431345853377 / 12500000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (28232433031 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12643_19 : CellCertificate 12643 (888289834794191 / 10000000000000000 : ℝ) (415337733110547 / 250000000000000000 : ℝ) (41952698407413 / 1250000000000000 : ℝ)
    (cell12643 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · norm_num [cell12643]
  · have h := gap_lower (n := 12643) (a := (2085405434109 / 2500000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451719719941 / 20000000000000 : ℝ))
      (E := (cell12643 ⟨19, by decide⟩).energy) (xi := (41952698407413 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12643 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12643]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12643])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12643) (a := (2085405434109 / 2500000000000 : ℝ)) (b := (162929556189 / 100000000000000 : ℝ)) (q := (451719719941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12643])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12643]

theorem cert12644_0 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (42038420706277 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129198935661 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨0, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (42038420706277 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129198935661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_1 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (8404184842903 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (141150117271 / 6250000000000 : ℝ))
      (E := (cell12644 ⟨1, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (8404184842903 / 10000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (141150117271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_2 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (42003440202613 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258405864549 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨2, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (42003440202613 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258405864549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_3 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16794387460917 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258409844927 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨3, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16794387460917 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258409844927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_4 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (4196850954537 / 5000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129206942039 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨4, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (4196850954537 / 5000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129206942039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_5 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41951062863759 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258417874679 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨5, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41951062863759 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258417874679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_6 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16773451435787 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258421882799 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨6, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16773451435787 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258421882799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_7 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41916206704599 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451685171681 / 20000000000000 : ℝ))
      (E := (cell12644 ⟨7, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41916206704599 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (451685171681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_8 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83797594382699 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (70575933347 / 3125000000000 : ℝ))
      (E := (cell12644 ⟨8, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83797594382699 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (70575933347 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_9 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41881400032009 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282304232289 / 12500000000000 : ℝ))
      (E := (cell12644 ⟨9, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41881400032009 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (282304232289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_10 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16353130941 / 19531250000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129218919569 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨10, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16353130941 / 19531250000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129218919569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_11 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (41846642704677 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129220937251 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨11, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (41846642704677 / 50000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129220937251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_12 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20914641250863 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (35288216483 / 1562500000000 : ℝ))
      (E := (cell12644 ⟨12, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20914641250863 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (35288216483 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_13 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (10452983645691 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258449844767 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨13, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (10452983645691 / 12500000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258449844767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_14 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83589197861077 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129226925089 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨14, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83589197861077 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129226925089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_15 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (20888637763943 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564614469253 / 25000000000000 : ℝ))
      (E := (cell12644 ⟨15, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (20888637763943 / 25000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (564614469253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_16 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16703985743093 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258461872713 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨16, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16703985743093 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258461872713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_17 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (16697066161237 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129232921293 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨17, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (16697066161237 / 20000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129232921293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_18 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83450757294137 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258469849923 / 100000000000000 : ℝ))
      (E := (cell12644 ⟨18, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83450757294137 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (2258469849923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12644_19 : CellCertificate 12644 (888261657777959 / 10000000000000000 : ℝ) (332243898927723 / 200000000000000000 : ℝ) (335594389180601 / 10000000000000000 : ℝ)
    (cell12644 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · norm_num [cell12644]
  · have h := gap_lower (n := 12644) (a := (83416208145701 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129236920683 / 50000000000000 : ℝ))
      (E := (cell12644 ⟨19, by decide⟩).energy) (xi := (335594389180601 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12644 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12644]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12644])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12644) (a := (83416208145701 / 100000000000000 : ℝ)) (b := (162916511493 / 100000000000000 : ℝ)) (q := (1129236920683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12644])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12644]

theorem cert12645_0 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (84076826150007 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258273109477 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨0, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (84076826150007 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258273109477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_1 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (3361673339549 / 4000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (451655427021 / 20000000000000 : ℝ))
      (E := (cell12645 ⟨1, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (3361673339549 / 4000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (451655427021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_2 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (84006865786707 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258281144709 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨2, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (84006865786707 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258281144709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_3 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20992980751849 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282285643407 / 12500000000000 : ℝ))
      (E := (cell12645 ⟨3, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20992980751849 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282285643407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_4 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (20984251278607 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258289151453 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨4, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (20984251278607 / 25000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258289151453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_5 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (8390211207163 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258293107827 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨5, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (8390211207163 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258293107827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_6 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83867243843019 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282287142549 / 12500000000000 : ℝ))
      (E := (cell12645 ⟨6, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83867243843019 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (282287142549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_7 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83832400392803 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (70571910663 / 3125000000000 : ℝ))
      (E := (cell12645 ⟨7, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83832400392803 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (70571910663 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_8 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41898790842687 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129152558957 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨8, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41898790842687 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129152558957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_9 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (16752557537063 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (112915456793 / 5000000000000 : ℝ))
      (E := (cell12645 ⟨9, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (16752557537063 / 20000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (112915456793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_10 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (8372801835739 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258313144193 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨10, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (8372801835739 / 10000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258313144193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_11 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (1673865473331 / 2000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564579287443 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨11, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (1673865473331 / 2000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564579287443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_12 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83658553577929 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258321101117 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨12, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83658553577929 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258321101117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_13 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (2090596451421 / 2500000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (70572660023 / 3125000000000 : ℝ))
      (E := (cell12645 ⟨13, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (2090596451421 / 2500000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (70572660023 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_14 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83589187068779 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129164549273 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨14, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83589187068779 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129164549273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_15 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83554540579421 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129166549249 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨15, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83554540579421 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129166549249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_16 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41759959277309 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129168563107 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨16, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41759959277309 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129168563107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_17 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (83485320960401 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129170564433 / 50000000000000 : ℝ))
      (E := (cell12645 ⟨17, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (83485320960401 / 100000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (1129170564433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_18 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (2607835867593 / 3125000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564586277879 / 25000000000000 : ℝ))
      (E := (cell12645 ⟨18, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (2607835867593 / 3125000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (564586277879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12645_19 : CellCertificate 12645 (444116742521343 / 5000000000000000 : ℝ) (830544038815401 / 500000000000000000 : ℝ) (335567195575943 / 10000000000000000 : ℝ)
    (cell12645 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · norm_num [cell12645]
  · have h := gap_lower (n := 12645) (a := (41708099464361 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258349137239 / 100000000000000 : ℝ))
      (E := (cell12645 ⟨19, by decide⟩).energy) (xi := (335567195575943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12645 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12645]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12645])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12645) (a := (41708099464361 / 50000000000000 : ℝ)) (b := (81451734451 / 50000000000000 : ℝ)) (q := (2258349137239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12645])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12645]

theorem cert12646_0 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (21019202722469 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258148458453 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨0, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (21019202722469 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258148458453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_1 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (84041818550797 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (282269055869 / 12500000000000 : ℝ))
      (E := (cell12646 ⟨1, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (84041818550797 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (282269055869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_2 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (42003425585263 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7056738813 / 312500000000 : ℝ))
      (E := (cell12646 ⟨2, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (42003425585263 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7056738813 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_3 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41985954356253 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564540111229 / 25000000000000 : ℝ))
      (E := (cell12646 ⟨3, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41985954356253 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (564540111229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_4 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (10492123892547 / 12500000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129082207099 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨4, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (10492123892547 / 12500000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129082207099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_5 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41951049208981 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225816845223 / 10000000000000 : ℝ))
      (E := (cell12646 ⟨5, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41951049208981 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (225816845223 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_6 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20966807627321 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129086225691 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨6, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20966807627321 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129086225691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_7 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83832387378549 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7056801311 / 312500000000 : ℝ))
      (E := (cell12646 ⟨7, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83832387378549 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (7056801311 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_8 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83797568990153 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258180422247 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨8, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83797568990153 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258180422247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_9 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (20940693827169 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129092233497 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨9, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (20940693827169 / 25000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129092233497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_10 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41864003149443 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258188444859 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨10, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41864003149443 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258188444859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_11 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41846630962867 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258192420691 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨11, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41846630962867 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258192420691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_12 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41829271077177 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258196459183 / 100000000000000 : ℝ))
      (E := (cell12646 ⟨12, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41829271077177 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (2258196459183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_13 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83623846950061 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451640090109 / 20000000000000 : ℝ))
      (E := (cell12646 ⟨13, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83623846950061 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (451640090109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_14 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (5224323517397 / 6250000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (45164089179 / 2000000000000 : ℝ))
      (E := (cell12646 ⟨14, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (5224323517397 / 6250000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (45164089179 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_15 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41777265052451 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129104216053 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨15, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41777265052451 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129104216053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_16 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41759954197783 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129106216871 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨16, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41759954197783 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129106216871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_17 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83485311116373 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (282277051379 / 12500000000000 : ℝ))
      (E := (cell12646 ⟨17, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83485311116373 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (282277051379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_18 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (83450738233531 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1102646693 / 48828125000 : ℝ))
      (E := (cell12646 ⟨18, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (83450738233531 / 100000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1102646693 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12646_19 : CellCertificate 12646 (888205316587347 / 10000000000000000 : ℝ) (830478340706907 / 500000000000000000 : ℝ) (2684320051553 / 80000000000000 : ℝ)
    (cell12646 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · norm_num [cell12646]
  · have h := gap_lower (n := 12646) (a := (41708094856711 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129112214539 / 50000000000000 : ℝ))
      (E := (cell12646 ⟨19, by decide⟩).energy) (xi := (2684320051553 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12646 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12646]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12646])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12646) (a := (41708094856711 / 50000000000000 : ℝ)) (b := (81445214207 / 50000000000000 : ℝ)) (q := (1129112214539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12646])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12646]

theorem cert12647_0 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (84076795632163 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129011901317 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨0, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (84076795632163 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129011901317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_1 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (42020901807623 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258027811877 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨1, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (42020901807623 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258027811877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_2 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (42003418278341 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258031806603 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨2, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (42003418278341 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258031806603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_3 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16794378883983 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112901789789 / 5000000000000 : ℝ))
      (E := (cell12647 ⟨3, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16794378883983 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (112901789789 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_4 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83936977168583 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (225803978811 / 10000000000000 : ℝ))
      (E := (cell12647 ⟨4, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83936977168583 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (225803978811 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_5 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16780416953303 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129021896021 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨5, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16780416953303 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129021896021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_6 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83867217177731 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451609563153 / 20000000000000 : ℝ))
      (E := (cell12647 ⟨6, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83867217177731 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451609563153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_7 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41916187183219 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258051809249 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨7, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41916187183219 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258051809249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_8 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16759511259407 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258055780101 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨8, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16759511259407 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258055780101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_9 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41881381467051 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (70564368553 / 3125000000000 : ℝ))
      (E := (cell12647 ⟨9, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41881381467051 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (70564368553 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_10 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83727994242407 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258063799173 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨10, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83727994242407 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258063799173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_11 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (10461656273363 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451613560677 / 20000000000000 : ℝ))
      (E := (cell12647 ⟨11, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (10461656273363 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (451613560677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_12 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41829265366363 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258071812939 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨12, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41829265366363 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258071812939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_13 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (83623835845191 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258075776083 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨13, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (83623835845191 / 100000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258075776083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_14 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (16717833097959 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258079756989 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨14, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (16717833097959 / 20000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258079756989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_15 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (10444314954027 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (28226047019 / 1250000000000 : ℝ))
      (E := (cell12647 ⟨15, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (10444314954027 / 12500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (28226047019 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_16 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (41759949119153 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129043897649 / 50000000000000 : ℝ))
      (E := (cell12647 ⟨16, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (41759949119153 / 50000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (1129043897649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_17 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (834853012741 / 1000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258091805491 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨17, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (834853012741 / 1000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258091805491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_18 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (20862682176451 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258095797163 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨18, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (20862682176451 / 25000000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258095797163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12647_19 : CellCertificate 12647 (444088576205461 / 5000000000000000 : ℝ) (830412652991359 / 500000000000000000 : ℝ) (335512821783943 / 10000000000000000 : ℝ)
    (cell12647 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · norm_num [cell12647]
  · have h := gap_lower (n := 12647) (a := (417080902499 / 500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258099775133 / 100000000000000 : ℝ))
      (E := (cell12647 ⟨19, by decide⟩).energy) (xi := (335512821783943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12647 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12647]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12647])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12647) (a := (417080902499 / 500000000000 : ℝ)) (b := (162877390031 / 100000000000000 : ℝ)) (q := (2258099775133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12647])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12647]

theorem cert12648_0 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (16815356075373 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257899199833 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨0, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (16815356075373 / 20000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257899199833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_1 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (10505223585259 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564475793013 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨1, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (10505223585259 / 12500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564475793013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_2 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (3360272877807 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257907188339 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨2, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (3360272877807 / 4000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257907188339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_3 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83971880129621 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257911199851 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨3, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83971880129621 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257911199851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_4 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83936963199049 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257915157393 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨4, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83936963199049 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257915157393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_5 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83902071117287 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564479796297 / 25000000000000 : ℝ))
      (E := (cell12648 ⟨5, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83902071117287 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (564479796297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_6 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83867203848357 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257923175603 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨6, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83867203848357 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257923175603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_7 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83832361356469 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (225792719447 / 10000000000000 : ℝ))
      (E := (cell12648 ⟨7, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83832361356469 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (225792719447 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_8 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83797543606019 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (56448279787 / 2500000000000 : ℝ))
      (E := (cell12648 ⟨8, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83797543606019 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (56448279787 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_9 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83762750561591 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257935173987 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨9, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83762750561591 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257935173987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_10 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41863991093977 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128969574549 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨10, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41863991093977 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128969574549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_11 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (4184661922503 / 5000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (225794318173 / 10000000000000 : ℝ))
      (E := (cell12648 ⟨11, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (4184661922503 / 5000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (225794318173 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_12 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (41829259656523 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128973581193 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨12, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (41829259656523 / 50000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128973581193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_13 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (8362382474223 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112897557773 / 5000000000000 : ℝ))
      (E := (cell12648 ⟨13, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (8362382474223 / 10000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (112897557773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_14 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83589154703109 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257955167063 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨14, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83589154703109 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257955167063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_15 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (1044431364517 / 1250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128979572451 / 50000000000000 : ℝ))
      (E := (cell12648 ⟨15, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (1044431364517 / 1250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (1128979572451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_16 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (2087997202071 / 2500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257963152703 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨16, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (2087997202071 / 2500000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257963152703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_17 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (83485291433581 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (7056147487 / 312500000000 : ℝ))
      (E := (cell12648 ⟨17, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (83485291433581 / 100000000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (7056147487 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_18 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (5215669948737 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257971162991 / 100000000000000 : ℝ))
      (E := (cell12648 ⟨18, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (5215669948737 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (2257971162991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12648_19 : CellCertificate 12648 (222037248128097 / 2500000000000000 : ℝ) (1660693951332583 / 1000000000000000000 : ℝ) (20967852599637 / 625000000000000 : ℝ)
    (cell12648 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · norm_num [cell12648]
  · have h := gap_lower (n := 12648) (a := (5213510705491 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (451595035081 / 20000000000000 : ℝ))
      (E := (cell12648 ⟨19, by decide⟩).energy) (xi := (20967852599637 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12648 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12648]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12648])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12648) (a := (5213510705491 / 6250000000000 : ℝ)) (b := (162864353751 / 100000000000000 : ℝ)) (q := (451595035081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12648])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12648]

theorem cert12649_0 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (42038382561991 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564443648061 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨0, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (42038382561991 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564443648061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_1 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (84041773751273 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257778585309 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨1, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (84041773751273 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257778585309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_2 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (42003403668003 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128891311609 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨2, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (42003403668003 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128891311609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_3 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (671774926733 / 800000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451557319851 / 20000000000000 : ℝ))
      (E := (cell12649 ⟨3, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (671774926733 / 800000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (451557319851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_4 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20984237307943 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (45155811599 / 2000000000000 : ℝ))
      (E := (cell12649 ⟨4, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20984237307943 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (45155811599 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_5 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41951028735139 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564448643437 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨5, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41951028735139 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564448643437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_6 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20966797630291 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257798588839 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨6, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20966797630291 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257798588839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_7 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (523952177179 / 625000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257802575187 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨7, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (523952177179 / 625000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257802575187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_8 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (16759506183421 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257806598393 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨8, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (16759506183421 / 20000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257806598393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_9 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83762738191143 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564452651967 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨9, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83762738191143 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564452651967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_10 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20931992533881 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564453652679 / 25000000000000 : ℝ))
      (E := (cell12649 ⟨10, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20931992533881 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (564453652679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_11 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (41846613357601 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257818613791 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨11, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (41846613357601 / 50000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257818613791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_12 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83658507895313 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257822623697 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨12, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83658507895313 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257822623697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_13 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83623813641177 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (56445664717 / 2500000000000 : ℝ))
      (E := (cell12649 ⟨13, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83623813641177 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (56445664717 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_14 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (20897285979573 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225783057291 / 10000000000000 : ℝ))
      (E := (cell12649 ⟨14, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (20897285979573 / 25000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (225783057291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_15 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (5222156168271 / 6250000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257834582251 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨15, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (5222156168271 / 6250000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257834582251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_16 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83519877929167 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128919311159 / 50000000000000 : ℝ))
      (E := (cell12649 ⟨16, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83519877929167 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (1128919311159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_17 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83485281594817 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257842582079 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨17, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83485281594817 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257842582079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_18 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (83450709655497 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (90313863319 / 4000000000000 : ℝ))
      (E := (cell12649 ⟨18, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (83450709655497 / 100000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (90313863319 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

theorem cert12649_19 : CellCertificate 12649 (888120836890723 / 10000000000000000 : ℝ) (1660562617458477 / 1000000000000000000 : ℝ) (335458465873669 / 10000000000000000 : ℝ)
    (cell12649 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · norm_num [cell12649]
  · have h := gap_lower (n := 12649) (a := (8341616207759 / 10000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257850571647 / 100000000000000 : ℝ))
      (E := (cell12649 ⟨19, by decide⟩).energy) (xi := (335458465873669 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12649 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12649]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12649])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12649) (a := (8341616207759 / 10000000000000 : ℝ)) (b := (162851319573 / 100000000000000 : ℝ)) (q := (2257850571647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12649])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12649]

end BstLean.Part268
