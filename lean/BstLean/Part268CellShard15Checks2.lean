import BstLean.Part268CellShard15Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12725_40 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41348014439253 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248572055379 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨40, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41348014439253 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248572055379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_41 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (8266203212711 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140536003643 / 6250000000000 : ℝ))
      (E := (cell12725 ⟨41, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (8266203212711 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140536003643 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_42 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82628058978001 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248580089303 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨42, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82628058978001 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248580089303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_43 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20648527350377 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140536505549 / 6250000000000 : ℝ))
      (E := (cell12725 ⟨43, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20648527350377 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140536505549 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_44 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20640045842027 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248588055623 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨44, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20640045842027 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248588055623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_45 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41263140424213 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281074013279 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨45, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41263140424213 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281074013279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_46 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82492401813237 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248596062537 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨46, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82492401813237 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248596062537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_47 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (4122927311673 / 5000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248600099457 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨47, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (4122927311673 / 5000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248600099457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_48 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41212357040081 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562151024321 / 25000000000000 : ℝ))
      (E := (cell12725 ⟨48, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41212357040081 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562151024321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_49 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20597726331139 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449721622559 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨49, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20597726331139 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449721622559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_50 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82357119937997 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248612084679 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨50, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82357119937997 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248612084679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_51 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (5145209868249 / 6250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248616128343 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨51, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (5145209868249 / 6250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248616128343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_52 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82289619158161 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248620123041 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨52, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82289619158161 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248620123041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_53 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (10281987963539 / 12500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562156031199 / 25000000000000 : ℝ))
      (E := (cell12725 ⟨53, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (10281987963539 / 12500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562156031199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_54 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82222211514361 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248628130437 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨54, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82222211514361 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248628130437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_55 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41094271274187 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449726427317 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨55, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41094271274187 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449726427317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_56 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82154896782557 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248636139647 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨56, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82154896782557 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248636139647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_57 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20530318547313 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562160033957 / 25000000000000 : ℝ))
      (E := (cell12725 ⟨57, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20530318547313 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562160033957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_58 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82087674740941 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281080522537 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨58, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82087674740941 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281080522537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_59 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41027049205121 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (56216203763 / 2500000000000 : ℝ))
      (E := (cell12725 ⟨59, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41027049205121 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (56216203763 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12726_40 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82696026230297 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124225109983 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨40, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82696026230297 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124225109983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_41 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82662029780643 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248454218889 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨41, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82662029780643 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248454218889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_42 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41314028466431 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562114546953 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨42, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41314028466431 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562114546953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_43 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (258106586429 / 312500000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248462184667 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨43, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (258106586429 / 312500000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248462184667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_44 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10320022740547 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449693241683 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨44, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10320022740547 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449693241683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_45 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10315784963097 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449694039787 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨45, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10315784963097 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449694039787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_46 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10311550121157 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281059276697 / 12500000000000 : ℝ))
      (E := (cell12726 ⟨46, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10311550121157 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281059276697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_47 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (16491709137747 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562119562663 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨47, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (16491709137747 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562119562663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_48 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82424713834283 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248482249323 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨48, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82424713834283 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248482249323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_49 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (8239090537711 / 10000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248486266367 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨49, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (8239090537711 / 10000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248486266367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_50 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41178560144287 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248490240469 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨50, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41178560144287 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248490240469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_51 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (3292934341607 / 4000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248494228029 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨51, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (3292934341607 / 4000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248494228029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_52 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82289620103557 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (89939931413 / 4000000000000 : ℝ))
      (E := (cell12726 ⟨52, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82289620103557 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (89939931413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_53 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10281988118813 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449700458271 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨53, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10281988118813 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449700458271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_54 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41111106526471 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449701260391 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨54, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41111106526471 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449701260391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_55 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41094272191469 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248510254641 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨55, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41094272191469 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248510254641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_56 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10269362364087 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562128566001 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨56, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10269362364087 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562128566001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_57 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41060638307281 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (70266195849 / 3125000000000 : ℝ))
      (E := (cell12726 ⟨57, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41060638307281 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (70266195849 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_58 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82087677461017 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (22485223193 / 1000000000000 : ℝ))
      (E := (cell12726 ⟨58, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82087677461017 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (22485223193 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_59 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (2051352535617 / 2500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248526297869 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨59, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (2051352535617 / 2500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248526297869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12727_40 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41348011791477 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248328381403 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨40, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41348011791477 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248328381403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_41 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82662027435007 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248332376377 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨41, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82662027435007 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248332376377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_42 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (16525610977703 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248336400841 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨42, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (16525610977703 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248336400841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_43 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (5162131619613 / 6250000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124170197577 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨43, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (5162131619613 / 6250000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124170197577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_44 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20640045120341 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248344358207 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨44, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20640045120341 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248344358207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_45 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (8252627856181 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248348406411 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨45, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (8252627856181 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248348406411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_46 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82492400125923 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248352420579 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨46, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82492400125923 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248352420579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_47 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82458545144623 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124178199479 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨47, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82458545144623 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124178199479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_48 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41212356794489 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (140522524907 / 6250000000000 : ℝ))
      (E := (cell12727 ⟨48, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41212356794489 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (140522524907 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_49 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82390905430203 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562091104281 / 25000000000000 : ℝ))
      (E := (cell12727 ⟨49, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82390905430203 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562091104281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_50 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41178560319827 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124184196741 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨50, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41178560319827 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124184196741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_51 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41161679594417 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224837244299 / 10000000000000 : ℝ))
      (E := (cell12727 ⟨51, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41161679594417 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224837244299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_52 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (10286202631173 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449675288981 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨52, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (10286202631173 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449675288981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_53 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20563976548273 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449676091049 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨53, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20563976548273 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449676091049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_54 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82222214591883 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248384470841 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨54, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82222214591883 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248384470841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_55 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (3287541848713 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449677685841 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨55, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (3287541848713 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449677685841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_56 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20538725260781 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248392444929 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨56, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20538725260781 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248392444929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_57 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (656970232321 / 800000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449679291027 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨57, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (656970232321 / 800000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449679291027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_58 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (8208768018131 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248400455819 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨58, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (8208768018131 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248400455819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_59 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (820541044393 / 1000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449680900393 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨59, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (820541044393 / 1000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449680900393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12728_40 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20674005234119 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248206598443 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨40, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20674005234119 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248206598443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_41 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82662025090199 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248210589529 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨41, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82662025090199 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248210589529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_42 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82628052844961 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248214551999 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨42, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82628052844961 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248214551999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_43 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20648526042773 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449643720521 / 20000000000000 : ℝ))
      (E := (cell12728 ⟨43, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20648526042773 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449643720521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_44 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (2580005594971 / 3125000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562055640961 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨44, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (2580005594971 / 3125000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562055640961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_45 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10315784677441 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248226610923 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨45, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10315784677441 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248226610923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_46 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82492399283237 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124115312329 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨46, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82492399283237 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124115312329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_47 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82458544601121 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248234603291 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨47, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82458544601121 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248234603291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_48 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82424713344249 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124119301893 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨48, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82424713344249 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124119301893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_49 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (16478181096767 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562060656007 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨49, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (16478181096767 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562060656007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_50 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41178560495619 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124123301351 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨50, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41178560495619 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124123301351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_51 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82323359837959 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562062663803 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨51, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82323359837959 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562062663803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_52 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41144810997821 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248254660813 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨52, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41144810997821 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248254660813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_53 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (3290236297443 / 4000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224825861647 / 10000000000000 : ℝ))
      (E := (cell12728 ⟨53, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (3290236297443 / 4000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224825861647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_54 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (5138888508199 / 6250000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281032829637 / 12500000000000 : ℝ))
      (E := (cell12728 ⟨54, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (5138888508199 / 6250000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281032829637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_55 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82188548053037 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124133330139 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨55, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82188548053037 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124133330139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_56 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (1026936289673 / 1250000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248270682423 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨56, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (1026936289673 / 1250000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248270682423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_57 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (4106064073297 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248274640583 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨57, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (4106064073297 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248274640583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_58 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (4104384145091 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248278649027 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨58, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (4104384145091 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248278649027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_59 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (820541074541 / 1000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124141351807 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨59, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (820541074541 / 1000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124141351807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12729_40 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (5168501143179 / 6250000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124042406167 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨40, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (5168501143179 / 6250000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124042406167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_41 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (4133101137311 / 5000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (224808879957 / 10000000000000 : ℝ))
      (E := (cell12729 ⟨41, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (4133101137311 / 5000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (224808879957 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_42 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82628050802199 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248092817679 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨42, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82628050802199 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248092817679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_43 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20648525607283 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (112404840351 / 5000000000000 : ℝ))
      (E := (cell12729 ⟨43, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20648525607283 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (112404840351 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_44 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82560177597499 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248100825327 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨44, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82560177597499 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248100825327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_45 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82526276277929 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89924192499 / 4000000000000 : ℝ))
      (E := (cell12729 ⟨45, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82526276277929 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89924192499 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_46 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41246199220599 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248108825813 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨46, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41246199220599 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248108825813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_47 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82458544058231 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248112863651 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨47, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82458544058231 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248112863651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_48 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (16484942620019 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248116865149 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨48, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (16484942620019 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248116865149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_49 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82390905538007 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124060414059 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨49, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82390905538007 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124060414059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_50 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (3294284853733 / 4000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248124868129 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨50, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (3294284853733 / 4000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248124868129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_51 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82323360487551 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124064432347 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨51, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82323360487551 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124064432347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_52 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20572405735583 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124066437009 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨52, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20572405735583 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124066437009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_53 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82255908679453 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248136893139 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨53, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82255908679453 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248136893139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_54 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20555554417711 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248140859801 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨54, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20555554417711 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248140859801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_55 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20547137472143 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124072444379 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨55, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20547137472143 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124072444379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_56 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20538726326211 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248148917361 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨56, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20538726326211 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248148917361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_57 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (10265160486501 / 12500000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248152882659 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨57, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (10265160486501 / 12500000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248152882659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_58 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82087685622547 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562039224731 / 25000000000000 : ℝ))
      (E := (cell12729 ⟨58, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82087685622547 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562039224731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_59 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82054110469083 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449632180563 / 20000000000000 : ℝ))
      (E := (cell12729 ⟨59, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82054110469083 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449632180563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12730_40 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82696015646117 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247963081831 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨40, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82696015646117 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247963081831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_41 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (8266202040307 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561991766319 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨41, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (8266202040307 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561991766319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_42 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (8262804876023 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247971080287 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨42, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (8262804876023 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247971080287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_43 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82594100687929 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247975067221 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨43, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82594100687929 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247975067221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_44 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82560176156647 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561994770953 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨44, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82560176156647 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561994770953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_45 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41263137568507 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449596613987 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨45, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41263137568507 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449596613987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_46 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82492397599807 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (280998385367 / 12500000000000 : ℝ))
      (E := (cell12730 ⟨46, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82492397599807 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (280998385367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_47 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82458543515951 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123995560563 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨47, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82458543515951 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123995560563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_48 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (20606178214129 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247995123663 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨48, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (20606178214129 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247995123663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_49 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82390905592717 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247999147321 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨49, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82390905592717 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247999147321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_50 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41178560847957 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (70250097837 / 3125000000000 : ℝ))
      (E := (cell12730 ⟨50, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41178560847957 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (70250097837 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_51 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82323361137611 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1124003565223 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨51, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82323361137611 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1124003565223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_52 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (20572405972363 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449602228711 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨52, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (20572405972363 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449602228711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_53 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82255909923227 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2248015167143 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨53, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82255909923227 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2248015167143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_54 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82222219210863 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1124009569479 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨54, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82222219210863 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1124009569479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_55 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (8218855172443 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1798418539 / 80000000000 : ℝ))
      (E := (cell12730 ⟨55, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (8218855172443 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1798418539 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_56 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (10269363429517 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2248027149743 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨56, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (10269363429517 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2248027149743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_57 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (10265160789791 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (281003897671 / 12500000000000 : ℝ))
      (E := (cell12730 ⟨57, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (10265160789791 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (281003897671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_58 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82087688343491 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (281004400689 / 12500000000000 : ℝ))
      (E := (cell12730 ⟨58, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82087688343491 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (281004400689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_59 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41027056742123 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (140502447423 / 6250000000000 : ℝ))
      (E := (cell12730 ⟨59, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41027056742123 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (140502447423 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12731_40 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16539202600447 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112392067409 / 5000000000000 : ℝ))
      (E := (cell12731 ⟨40, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16539202600447 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112392067409 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_41 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20665504515187 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247845386647 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨41, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20665504515187 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247845386647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_42 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82628046719053 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112392469931 / 5000000000000 : ℝ))
      (E := (cell12731 ⟨42, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82628046719053 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112392469931 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_43 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (2064852473687 / 2500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224785338321 / 10000000000000 : ℝ))
      (E := (cell12731 ⟨43, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (2064852473687 / 2500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224785338321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_44 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82560174716513 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449571479629 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨44, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82560174716513 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449571479629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_45 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82526273996781 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123930691651 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨45, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82526273996781 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123930691651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_46 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41246198379531 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247865396027 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨46, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41246198379531 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247865396027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_47 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41229271487141 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247869434629 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨47, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41229271487141 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247869434629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_48 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82424712613511 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123936719133 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨48, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82424712613511 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123936719133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_49 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41195452823983 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247877404749 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨49, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41195452823983 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247877404749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_50 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41178561024503 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247881449647 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨50, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41178561024503 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247881449647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_51 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82323361788137 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561971363117 / 25000000000000 : ℝ))
      (E := (cell12731 ⟨51, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82323361788137 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561971363117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_52 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82289624837003 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247889469421 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨52, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82289624837003 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247889469421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_53 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16451182233479 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247893438483 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨53, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16451182233479 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247893438483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_54 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41111110375621 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449579494913 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨54, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41111110375621 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449579494913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_55 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20547138390153 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247901456149 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨55, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20547138390153 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247901456149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_56 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20538727391929 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280988179837 / 12500000000000 : ℝ))
      (E := (cell12731 ⟨56, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20538727391929 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280988179837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_57 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (821212887449 / 1000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247909477557 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨57, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (821212887449 / 1000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247909477557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_58 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82087691064651 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449582690089 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨58, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82087691064651 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449582690089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_59 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82054116499591 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224791747147 / 10000000000000 : ℝ))
      (E := (cell12731 ⟨59, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82054116499591 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224791747147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12732_40 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82696010359217 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123859864443 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨40, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82696010359217 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123859864443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_41 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41331007859627 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224772370491 / 10000000000000 : ℝ))
      (E := (cell12732 ⟨41, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41331007859627 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224772370491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_42 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82628044678667 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561931928471 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨42, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82628044678667 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561931928471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_43 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82594097207787 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449546339233 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨43, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82594097207787 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449546339233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_44 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82560173277099 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247735709481 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨44, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82560173277099 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247735709481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_45 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82526272857231 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247739752579 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨45, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82526272857231 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247739752579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_46 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20623098979741 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (70241992659 / 3125000000000 : ℝ))
      (E := (cell12732 ⟨46, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20623098979741 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (70241992659 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_47 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (10307317804153 / 12500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247747745247 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨47, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (10307317804153 / 12500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247747745247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_48 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82424712371081 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247751750021 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨48, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82424712371081 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247751750021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_49 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82390905703753 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224775577729 / 10000000000000 : ℝ))
      (E := (cell12732 ⟨49, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82390905703753 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224775577729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_50 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (411785612013 / 500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247759765737 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨50, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (411785612013 / 500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247759765737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_51 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82323362439129 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247763771753 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨51, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82323362439129 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247763771753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_52 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (16457925156997 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247767792587 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨52, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (16457925156997 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247767792587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_53 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82255912411959 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247771766213 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨53, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82255912411959 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247771766213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_54 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82222222291979 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449555161509 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨54, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82222222291979 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449555161509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_55 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41094277698559 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (112388989753 / 5000000000000 : ℝ))
      (E := (cell12732 ⟨55, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41094277698559 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (112388989753 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_56 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82154911699583 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123891892111 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨56, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82154911699583 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123891892111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_57 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (3284851646869 / 4000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247787830377 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨57, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (3284851646869 / 4000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247787830377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_58 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20521923446507 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123895905621 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨58, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20521923446507 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123895905621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_59 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20513529878779 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (89911833637 / 4000000000000 : ℝ))
      (E := (cell12732 ⟨59, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20513529878779 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (89911833637 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12733_40 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82696007717063 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (140474881653 / 6250000000000 : ℝ))
      (E := (cell12733 ⟨40, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82696007717063 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (140474881653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_41 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (20665503344647 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247602078841 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨41, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (20665503344647 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247602078841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_42 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82628042639073 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561901521219 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨42, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82628042639073 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561901521219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_43 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (1651881909377 / 2000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561902516227 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨43, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (1651881909377 / 2000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561902516227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_44 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82560171838403 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247614076669 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨44, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82560171838403 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247614076669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_45 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (20631567929591 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123809059449 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨45, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (20631567929591 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123809059449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_46 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82492395079513 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561905532807 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨46, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82492395079513 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561905532807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_47 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (3298341675711 / 4000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123813055949 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨47, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (3298341675711 / 4000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123813055949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_48 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (3296988485169 / 4000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561907529467 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨48, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (3296988485169 / 4000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561907529467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_49 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41195452880039 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123817073511 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨49, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41195452880039 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123817073511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_50 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82357122756697 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123819069019 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨50, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82357122756697 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123819069019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_51 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82323363090587 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (140477634207 / 6250000000000 : ℝ))
      (E := (cell12733 ⟨51, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82323363090587 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (140477634207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_52 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82289626733397 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247646172087 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨52, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82289626733397 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247646172087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_53 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82255913656917 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247650150337 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨53, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82255913656917 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247650150337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_54 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (20555555958269 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123827068949 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨54, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (20555555958269 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123827068949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_55 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41094278616973 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449531638097 / 20000000000000 : ℝ))
      (E := (cell12733 ⟨55, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41094278616973 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449531638097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_56 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41077456915869 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247662186321 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨56, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41077456915869 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247662186321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_57 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82121293598801 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123833090341 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨57, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82121293598801 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123833090341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_58 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82087696507621 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (56191754239 / 2500000000000 : ℝ))
      (E := (cell12733 ⟨58, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82087696507621 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (56191754239 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_59 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82054122530823 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (35119909499 / 1562500000000 : ℝ))
      (E := (cell12733 ⟨59, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82054122530823 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (35119909499 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12734_40 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41348002537887 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123738240433 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨40, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41348002537887 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123738240433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_41 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (66129608831 / 80000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56187012711 / 2500000000000 : ℝ))
      (E := (cell12734 ⟨41, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (66129608831 / 80000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56187012711 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_42 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82628040600269 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247484511597 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨42, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82628040600269 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247484511597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_43 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82594093730667 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123744244721 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨43, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82594093730667 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123744244721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_44 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41280085200213 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449498499941 / 20000000000000 : ℝ))
      (E := (cell12734 ⟨44, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41280085200213 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449498499941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_45 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82526270580179 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247496482259 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨45, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82526270580179 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247496482259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_46 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82492394240707 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140468780903 / 6250000000000 : ℝ))
      (E := (cell12734 ⟨46, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82492394240707 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140468780903 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_47 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82458541352937 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247504534579 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨47, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82458541352937 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247504534579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_48 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41212355943971 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140469283863 / 6250000000000 : ℝ))
      (E := (cell12734 ⟨48, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41212355943971 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140469283863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_49 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82390905816941 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247512513943 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨49, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82390905816941 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247512513943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_50 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (643415024307 / 781250000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247516507567 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨50, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (643415024307 / 781250000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247516507567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_51 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (5145210233907 / 6250000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123760260067 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨51, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (5145210233907 / 6250000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123760260067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_52 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (257155086507 / 312500000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449504909777 / 20000000000000 : ℝ))
      (E := (cell12734 ⟨52, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (257155086507 / 312500000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449504909777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_53 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82255914902269 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247528531799 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨53, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82255914902269 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247528531799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_54 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82222225374531 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449506516757 / 20000000000000 : ℝ))
      (E := (cell12734 ⟨54, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82222225374531 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449506516757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_55 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41094279535549 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56188414583 / 2500000000000 : ℝ))
      (E := (cell12734 ⟨55, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41094279535549 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56188414583 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_56 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82154915964181 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123770292933 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨56, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82154915964181 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123770292933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_57 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82121296026129 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112377229381 / 5000000000000 : ℝ))
      (E := (cell12734 ⟨57, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82121296026129 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112377229381 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_58 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (8208769922943 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247548584571 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨58, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (8208769922943 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247548584571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_59 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (8205412554671 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247552572503 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨59, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (8205412554671 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247552572503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12735_40 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20674000608837 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123677455447 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨40, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20674000608837 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123677455447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_41 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82662008699739 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (449471786987 / 20000000000000 : ℝ))
      (E := (cell12735 ⟨41, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82662008699739 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (449471786987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_42 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82628038562257 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247362935251 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨42, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82628038562257 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247362935251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_43 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41297045996619 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123683455473 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨43, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41297045996619 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123683455473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_44 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82560168963167 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247370919749 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨44, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82560168963167 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247370919749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_45 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82526269442677 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247374960401 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨45, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82526269442677 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247374960401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_46 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20623098350637 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (56184472841 / 2500000000000 : ℝ))
      (E := (cell12735 ⟨46, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20623098350637 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (56184472841 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_47 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82458540813709 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247382954379 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨47, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82458540813709 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247382954379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_48 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41212355823617 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123693481451 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨48, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41212355823617 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123693481451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_49 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41195452937171 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247390937019 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨49, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41195452937171 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247390937019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_50 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20589280866599 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (280924374037 / 12500000000000 : ℝ))
      (E := (cell12735 ⟨50, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20589280866599 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (280924374037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_51 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82323364394903 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224739894923 / 10000000000000 : ℝ))
      (E := (cell12735 ⟨51, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82323364394903 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224739894923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_52 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (10286203578939 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247402982021 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨52, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (10286203578939 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247402982021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_53 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (5140994759251 / 6250000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (449481393931 / 20000000000000 : ℝ))
      (E := (cell12735 ⟨53, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (5140994759251 / 6250000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (449481393931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_54 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (16444445383269 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247410967967 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨54, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (16444445383269 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247410967967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_55 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20547140227143 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (17557929481 / 781250000000 : ℝ))
      (E := (cell12735 ⟨55, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20547140227143 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (17557929481 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_56 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (8215491809691 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247418982861 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨56, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (8215491809691 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247418982861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_57 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82121298453709 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123711496021 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨57, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82121298453709 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123711496021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_58 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (2565240685983 / 3125000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247426997103 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨58, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (2565240685983 / 3125000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247426997103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_59 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82054128562777 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (89897239753 / 4000000000000 : ℝ))
      (E := (cell12735 ⟨59, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82054128562777 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (89897239753 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12736_40 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41347999897893 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247233396531 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨40, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41347999897893 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247233396531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_41 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (16532401272311 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123618679163 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨41, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (16532401272311 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123618679163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_42 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20657009131259 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449448282927 / 20000000000000 : ℝ))
      (E := (cell12736 ⟨42, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20657009131259 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449448282927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_43 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (16518818051313 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (28090567353 / 1250000000000 : ℝ))
      (E := (cell12736 ⟨43, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (16518818051313 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (28090567353 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_44 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41280083763313 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123624697823 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨44, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41280083763313 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123624697823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_45 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (1289472942279 / 1562500000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247253376719 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨45, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (1289472942279 / 1562500000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247253376719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_46 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41246196282517 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247257388807 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨46, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41246196282517 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247257388807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_47 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82458540275091 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561815357553 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨47, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82458540275091 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561815357553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_48 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82424711407099 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561816360023 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨48, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82424711407099 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561816360023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_49 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82390905932281 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1797815533 / 80000000000 : ℝ))
      (E := (cell12736 ⟨49, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82390905932281 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1797815533 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_50 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41178561910999 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (224727341527 / 10000000000000 : ℝ))
      (E := (cell12736 ⟨50, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41178561910999 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (224727341527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_51 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82323365047759 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247277434603 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨51, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82323365047759 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247277434603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_52 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (16457925916243 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123640706229 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨52, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (16457925916243 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123640706229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_53 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20563979348539 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561821365977 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨53, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20563979348539 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561821365977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_54 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82222228458517 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449457893537 / 20000000000000 : ℝ))
      (E := (cell12736 ⟨54, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82222228458517 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449457893537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_55 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82188562746369 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449458695887 / 20000000000000 : ℝ))
      (E := (cell12736 ⟨55, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82188562746369 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449458695887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_56 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82154920229927 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247297495557 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨56, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82154920229927 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247297495557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_57 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (4106065044077 / 5000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247301453101 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨57, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (4106065044077 / 5000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247301453101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_58 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82087704673697 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247305466331 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨58, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82087704673697 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247305466331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_59 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (3282165263161 / 4000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247309471903 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨59, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (3282165263161 / 4000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247309471903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12737_40 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82695997157087 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561777969757 / 25000000000000 : ℝ))
      (E := (cell12737 ⟨40, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82695997157087 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561777969757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_41 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41331002012099 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123557948081 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨41, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41331002012099 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123557948081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_42 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (16525606897721 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123559945477 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨42, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (16525606897721 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123559945477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_43 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (16518817704129 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247123862507 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨43, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (16518817704129 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247123862507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_44 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20640041522701 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (44942557371 / 2000000000000 : ℝ))
      (E := (cell12737 ⟨44, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20640041522701 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (44942557371 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_45 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82526267169717 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (112356595391 / 5000000000000 : ℝ))
      (E := (cell12737 ⟨45, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82526267169717 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (112356595391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_46 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41246195864083 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247135919947 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨46, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41246195864083 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247135919947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_47 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41229269868541 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449427980633 / 20000000000000 : ℝ))
      (E := (cell12737 ⟨47, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41229269868541 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449427980633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_48 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41212355583769 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561785978609 / 25000000000000 : ℝ))
      (E := (cell12737 ⟨48, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41212355583769 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561785978609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_49 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82390905990757 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247147892673 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨49, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82390905990757 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247147892673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_50 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41178562089051 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247151953443 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨50, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41178562089051 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247151953443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_51 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82323365701081 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247155917241 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨51, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82323365701081 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247155917241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_52 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82289630531347 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280894994783 / 12500000000000 : ℝ))
      (E := (cell12737 ⟨52, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82289630531347 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280894994783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_53 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82255918640691 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (4494327911 / 200000000000 : ℝ))
      (E := (cell12737 ⟨53, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82255918640691 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (4494327911 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_54 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82222230001047 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (112358398239 / 5000000000000 : ℝ))
      (E := (cell12737 ⟨54, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82222230001047 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (112358398239 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_55 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82188564584489 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123585991357 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨55, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82188564584489 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123585991357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_56 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (8215492236323 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247175946577 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨56, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (8215492236323 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247175946577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_57 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41060651654811 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561794992699 / 25000000000000 : ℝ))
      (E := (cell12737 ⟨57, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41060651654811 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561794992699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_58 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41043853698077 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449436798451 / 20000000000000 : ℝ))
      (E := (cell12737 ⟨58, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41043853698077 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449436798451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_59 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41027067297727 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449437601347 / 20000000000000 : ℝ))
      (E := (cell12737 ⟨59, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41027067297727 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449437601347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12738_40 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20673998629813 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449398083427 / 20000000000000 : ℝ))
      (E := (cell12738 ⟨40, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20673998629813 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449398083427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_41 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20665500421917 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449398886179 / 20000000000000 : ℝ))
      (E := (cell12738 ⟨41, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20665500421917 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449398886179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_42 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20657008113241 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123499211503 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨42, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20657008113241 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123499211503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_43 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82594086785479 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247002392567 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨43, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82594086785479 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247002392567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_44 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82560164655699 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561751599327 / 25000000000000 : ℝ))
      (E := (cell12738 ⟨44, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82560164655699 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561751599327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_45 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82526266034259 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247010435967 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨45, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82526266034259 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247010435967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_46 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82492390891943 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247014448171 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨46, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82492390891943 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247014448171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_47 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41229269599841 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123509216077 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨47, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41229269599841 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123509216077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_48 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (1648494218571 / 2000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247022444877 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨48, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (1648494218571 / 2000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247022444877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_49 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (8239090604977 / 10000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123513212627 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨49, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (8239090604977 / 10000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123513212627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_50 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41178562267353 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247030429863 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨50, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41178562267353 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247030429863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_51 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82323366354869 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561758614039 / 25000000000000 : ℝ))
      (E := (cell12738 ⟨51, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82323366354869 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561758614039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_52 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82289631481909 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247038442341 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨52, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82289631481909 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247038442341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_53 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82255919887619 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (224704250349 / 10000000000000 : ℝ))
      (E := (cell12738 ⟨53, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82255919887619 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (224704250349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_54 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (16444446308787 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561761614813 / 25000000000000 : ℝ))
      (E := (cell12738 ⟨54, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (16444446308787 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561761614813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_55 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82188566422931 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247050483407 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨55, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82188566422931 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247050483407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_56 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (4107746224841 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247054513301 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨56, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (4107746224841 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247054513301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_57 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20530326434489 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247058485977 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨57, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20530326434489 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2247058485977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_58 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82087710118827 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123531257851 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨58, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82087710118827 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123531257851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_59 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82054137612063 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280883317391 / 12500000000000 : ℝ))
      (E := (cell12738 ⟨59, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82054137612063 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280883317391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12739_40 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82695991882279 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280858619013 / 12500000000000 : ℝ))
      (E := (cell12739 ⟨40, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82695991882279 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280858619013 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_41 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20665499837991 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246872962527 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨41, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20665499837991 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246872962527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_42 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41314015209057 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280859618999 / 12500000000000 : ℝ))
      (E := (cell12739 ⟨42, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41314015209057 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280859618999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_43 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82594085051067 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246880978421 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨43, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82594085051067 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246880978421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_44 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82560163221311 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123442490961 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨44, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82560163221311 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123442490961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_45 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82526264899483 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246889020029 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨45, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82526264899483 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246889020029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_46 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41246195028183 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123446486739 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨46, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41246195028183 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123446486739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_47 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82458538662891 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246897017179 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨47, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82458538662891 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246897017179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_48 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16484942138027 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449380206283 / 20000000000000 : ℝ))
      (E := (cell12739 ⟨48, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16484942138027 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449380206283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_49 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (2059772652733 / 2500000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246905013991 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨49, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (2059772652733 / 2500000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246905013991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_50 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20589281222953 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123454510743 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨50, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20589281222953 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123454510743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_51 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41161683504561 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246913051349 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨51, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41161683504561 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246913051349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_52 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (822896324329 / 1000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224691704179 / 10000000000000 : ℝ))
      (E := (cell12739 ⟨52, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (822896324329 / 1000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224691704179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_53 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41127960567471 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246921048821 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨53, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41127960567471 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246921048821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_54 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41111116543591 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246925069261 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨54, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41111116543591 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246925069261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_55 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16437713652339 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246929040619 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨55, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16437713652339 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246929040619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_56 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82154926630697 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561733269369 / 25000000000000 : ℝ))
      (E := (cell12739 ⟨56, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82154926630697 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561733269369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_57 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (4106065408327 / 5000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246937057797 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨57, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (4106065408327 / 5000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246937057797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_58 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20521928210429 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246941095847 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨58, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20521928210429 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246941095847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_59 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20513535157213 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (56173626727 / 2500000000000 : ℝ))
      (E := (cell12739 ⟨59, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20513535157213 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (56173626727 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12740_40 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (10336998655771 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (70210860709 / 3125000000000 : ℝ))
      (E := (cell12740 ⟨40, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (10336998655771 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (70210860709 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_41 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41330998508543 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449350309967 / 20000000000000 : ℝ))
      (E := (cell12740 ⟨41, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41330998508543 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449350309967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_42 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82628028384053 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246755595513 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨42, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82628028384053 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246755595513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_43 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (2581065103669 / 3125000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246759561251 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨43, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (2581065103669 / 3125000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246759561251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_44 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82560161787641 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561690890887 / 25000000000000 : ℝ))
      (E := (cell12740 ⟨44, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82560161787641 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561690890887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_45 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (20631565941347 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (112338380057 / 5000000000000 : ℝ))
      (E := (cell12740 ⟨45, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (20631565941347 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (112338380057 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_46 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82492389221433 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (280846451707 / 12500000000000 : ℝ))
      (E := (cell12740 ⟨46, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82492389221433 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (280846451707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_47 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82458538126709 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246775599327 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨47, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82458538126709 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246775599327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_48 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82424710452293 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246779615113 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨48, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82424710452293 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246779615113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_49 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82390906169407 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (89871343997 / 4000000000000 : ℝ))
      (E := (cell12740 ⟨49, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82390906169407 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (89871343997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_50 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82357125249419 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123393805171 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨50, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82357125249419 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123393805171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_51 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82323367663839 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246791643813 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨51, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82323367663839 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246791643813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_52 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (128577552163 / 156250000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449359127709 / 20000000000000 : ℝ))
      (E := (cell12740 ⟨52, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (128577552163 / 156250000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449359127709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_53 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82255922382657 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (280849956319 / 12500000000000 : ℝ))
      (E := (cell12740 ⟨53, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82255922382657 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (280849956319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_54 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41111117315393 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246803617571 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨54, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41111117315393 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246803617571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_55 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41094285050391 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246807654349 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨55, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41094285050391 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246807654349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_56 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82154928764861 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246811639103 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨56, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82154928764861 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246811639103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_57 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (5132581912211 / 6250000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246815686257 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨57, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (5132581912211 / 6250000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246815686257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_58 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (4104385778241 / 5000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246819673517 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨58, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (4104385778241 / 5000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246819673517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_59 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82054143645821 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246823655793 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨59, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82054143645821 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246823655793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12741_40 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (2067399665273 / 2500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561656547221 / 25000000000000 : ℝ))
      (E := (cell12741 ⟨40, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (2067399665273 / 2500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561656547221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_41 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41330997341517 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (140414387051 / 6250000000000 : ℝ))
      (E := (cell12741 ⟨41, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41330997341517 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (140414387051 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_42 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82628026350781 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246634177173 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨42, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82628026350781 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246634177173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_43 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82594081584503 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17973105599 / 800000000000 : ℝ))
      (E := (cell12741 ⟨43, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82594081584503 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17973105599 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_44 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (645001252771 / 781250000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246642201029 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨44, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (645001252771 / 781250000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246642201029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_45 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82526262631973 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280830779771 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨45, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82526262631973 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280830779771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_46 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (16498477677429 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246650250919 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨46, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (16498477677429 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246650250919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_47 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (2576829299723 / 3125000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280831779689 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨47, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (2576829299723 / 3125000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280831779689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_48 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82424710215023 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561664563727 / 25000000000000 : ℝ))
      (E := (cell12741 ⟨48, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82424710215023 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561664563727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_49 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82390906230031 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (70208195063 / 3125000000000 : ℝ))
      (E := (cell12741 ⟨49, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82390906230031 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (70208195063 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_50 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82357125607527 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449333251083 / 20000000000000 : ℝ))
      (E := (cell12741 ⟨50, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82357125607527 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449333251083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_51 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41161684159511 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449334046709 / 20000000000000 : ℝ))
      (E := (cell12741 ⟨51, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41161684159511 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449334046709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_52 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (8228963433617 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449334846521 / 20000000000000 : ℝ))
      (E := (cell12741 ⟨52, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (8228963433617 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449334846521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_53 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41127961815383 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17973425997 / 800000000000 : ℝ))
      (E := (cell12741 ⟨53, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41127961815383 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17973425997 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_54 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82222236174747 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112334114071 / 5000000000000 : ℝ))
      (E := (cell12741 ⟨54, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82222236174747 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112334114071 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_55 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (8218857194019 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280835783187 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨55, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (8218857194019 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280835783187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_56 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (8215493089931 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (224669025731 / 10000000000000 : ℝ))
      (E := (cell12741 ⟨56, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (8215493089931 / 10000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (224669025731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_57 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82121313024463 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246694312203 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨57, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82121313024463 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246694312203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_58 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82087718288139 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123349153943 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨58, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82087718288139 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123349153943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_59 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82054146662969 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17552361713 / 781250000000 : ℝ))
      (E := (cell12741 ⟨59, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82054146662969 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (17552361713 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12742_40 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41347991988267 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449300966389 / 20000000000000 : ℝ))
      (E := (cell12742 ⟨40, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41347991988267 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449300966389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_41 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82661992349807 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (22465088327 / 1000000000000 : ℝ))
      (E := (cell12742 ⟨41, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82661992349807 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (22465088327 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_42 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82628024318299 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280814109171 / 12500000000000 : ℝ))
      (E := (cell12742 ⟨42, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82628024318299 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280814109171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_43 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82594079852351 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246516894297 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨43, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82594079852351 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246516894297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_44 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82560158922451 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246520894369 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨44, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82560158922451 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246520894369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_45 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82526261499239 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246524872247 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨45, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82526261499239 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246524872247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_46 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41246193776751 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561632221317 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨46, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41246193776751 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561632221317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_47 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82458537056171 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123266436411 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨47, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82458537056171 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123266436411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_48 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41212354989163 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449307378373 / 20000000000000 : ℝ))
      (E := (cell12742 ⟨48, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41212354989163 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449307378373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_49 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82390906291191 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246540881307 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨49, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82390906291191 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246540881307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_50 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (16471425193227 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (89861795909 / 4000000000000 : ℝ))
      (E := (cell12742 ⟨50, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (16471425193227 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (89861795909 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_51 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82323368974669 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280818617321 / 12500000000000 : ℝ))
      (E := (cell12742 ⟨51, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82323368974669 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280818617321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_52 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (642887775691 / 781250000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246552942041 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨52, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (642887775691 / 781250000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246552942041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_53 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (20563981219817 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (22465569051 / 1000000000000 : ℝ))
      (E := (cell12742 ⟨53, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (20563981219817 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (22465569051 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_54 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82222237719067 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (44931218853 / 2000000000000 : ℝ))
      (E := (cell12742 ⟨54, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82222237719067 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (44931218853 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_55 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (1027357172249 / 1250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449312986633 / 20000000000000 : ℝ))
      (E := (cell12742 ⟨55, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (1027357172249 / 1250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449312986633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_56 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82154933034047 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246568932097 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨56, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82154933034047 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246568932097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_57 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (410606577269 / 500000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123286467821 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨57, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (410606577269 / 500000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123286467821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_58 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41043860505837 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123288469891 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨58, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41043860505837 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123288469891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_59 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41027074840149 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246580940297 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨59, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41027074840149 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246580940297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12743_40 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82695981343009 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (17549871333 / 781250000000 : ℝ))
      (E := (cell12743 ⟨40, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82695981343009 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (17549871333 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_41 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41330995008703 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112319376413 / 5000000000000 : ℝ))
      (E := (cell12743 ⟨41, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41330995008703 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112319376413 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_42 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41314011143303 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246391566503 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨42, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41314011143303 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246391566503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_43 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82594078120951 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123197792849 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨43, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82594078120951 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123197792849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_44 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82560157490931 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (561599896181 / 25000000000000 : ℝ))
      (E := (cell12743 ⟨44, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82560157490931 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (561599896181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_45 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41263130183593 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449280712449 / 20000000000000 : ℝ))
      (E := (cell12743 ⟨45, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41263130183593 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449280712449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_46 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41246193360251 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246407575599 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨46, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41246193360251 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246407575599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_47 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41229268260907 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246411564173 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨47, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41229268260907 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246411564173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_48 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82424709742201 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246415584923 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨48, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82424709742201 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246415584923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_49 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (10298863294111 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123209788379 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨49, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (10298863294111 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123209788379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_50 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82357126325243 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (70200737383 / 3125000000000 : ℝ))
      (E := (cell12743 ⟨50, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82357126325243 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (70200737383 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_51 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82323369630781 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123213790927 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨51, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82323369630781 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123213790927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_52 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16457927248231 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280803948719 / 12500000000000 : ℝ))
      (E := (cell12743 ⟨52, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16457927248231 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280803948719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_53 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82255926128163 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246435616977 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨53, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82255926128163 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246435616977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_54 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82222239263743 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123219800631 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨54, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82222239263743 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123219800631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_55 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20547143904993 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449288731471 / 20000000000000 : ℝ))
      (E := (cell12743 ⟨55, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20547143904993 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449288731471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_56 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82154935169069 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246447663467 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨56, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82154935169069 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246447663467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_57 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20530329470847 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246451674873 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨57, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20530329470847 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246451674873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_58 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82087723735423 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112322781419 / 5000000000000 : ℝ))
      (E := (cell12743 ⟨58, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82087723735423 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112322781419 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_59 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41027076348903 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246459638093 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨59, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41027076348903 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246459638093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12744_40 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41347989355173 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123131142459 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨40, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41347989355173 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123131142459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_41 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (8266198768583 / 10000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246266279499 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨41, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (8266198768583 / 10000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246266279499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_42 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41314010127851 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246270256577 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨42, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41314010127851 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246270256577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_43 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (2581064887197 / 3125000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123137137037 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨43, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (2581064887197 / 3125000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123137137037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_44 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (2580004876879 / 3125000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246278272091 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨44, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (2580004876879 / 3125000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246278272091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_45 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82526259235813 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123141154081 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨45, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82526259235813 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123141154081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_46 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82492385888147 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (224628632191 / 10000000000000 : ℝ))
      (E := (cell12744 ⟨46, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82492385888147 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (224628632191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_47 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (16491707197613 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449258062313 / 20000000000000 : ℝ))
      (E := (cell12744 ⟨47, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (16491707197613 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449258062313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_48 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (10303088688331 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246294334081 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨48, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (10303088688331 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246294334081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_49 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (1029886330189 / 1250000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246298328371 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨49, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (1029886330189 / 1250000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246298328371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_50 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20589281671213 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (70196948469 / 3125000000000 : ℝ))
      (E := (cell12744 ⟨50, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20589281671213 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (70196948469 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_51 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82323370287357 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246306340431 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨51, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82323370287357 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246306340431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_52 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82289637194291 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123155176419 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨52, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82289637194291 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123155176419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_53 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82255927377451 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123157163099 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨53, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82255927377451 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123157163099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_54 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82222240808777 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280789796927 / 12500000000000 : ℝ))
      (E := (cell12744 ⟨54, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82222240808777 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280789796927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_55 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41094288730173 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123161189481 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨55, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41094288730173 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123161189481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_56 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82154937304377 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561581598073 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨56, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82154937304377 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561581598073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_57 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41060660156613 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246330352443 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨57, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41060660156613 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246330352443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_58 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20521931614847 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246334373679 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨58, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20521931614847 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246334373679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_59 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41027077857747 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246338392649 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨59, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41027077857747 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246338392649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12745_40 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (5168498504909 / 6250000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (28076762951 / 1250000000000 : ℝ))
      (E := (cell12745 ⟨40, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (5168498504909 / 6250000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (28076762951 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_41 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82661985355079 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246145027641 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨41, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82661985355079 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246145027641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_42 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41314009112793 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246149061191 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨42, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41314009112793 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246149061191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_43 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82594074660409 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246153018251 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨43, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82594074660409 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246153018251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_44 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (2064003865751 / 2500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123078537083 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨44, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (2064003865751 / 2500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123078537083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_45 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82526258105119 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246161051133 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨45, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82526258105119 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246161051133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_46 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (20623096264109 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224616506531 / 10000000000000 : ℝ))
      (E := (cell12745 ⟨46, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (20623096264109 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224616506531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_47 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (20614633863731 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123084528041 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨47, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (20614633863731 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123084528041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_48 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82424709271667 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246173080403 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨48, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82424709271667 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246173080403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_49 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82390906477889 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246177077183 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨49, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82390906477889 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246177077183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_50 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82357127044961 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246181102997 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨50, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82357127044961 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246181102997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_51 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41161685472199 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246185096281 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨51, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41161685472199 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246185096281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_52 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (16457927629571 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123094556617 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨52, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (16457927629571 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123094556617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_53 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (20563982156783 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246193091823 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨53, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (20563982156783 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246193091823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_54 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82222242354167 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123098543937 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨54, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82222242354167 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123098543937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_55 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82188579301041 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224620109799 / 10000000000000 : ℝ))
      (E := (cell12745 ⟨55, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82188579301041 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224620109799 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_56 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82154939439971 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561551279643 / 25000000000000 : ℝ))
      (E := (cell12745 ⟨56, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82154939439971 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561551279643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_57 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41060661371657 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246209145809 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨57, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41060661371657 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246209145809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_58 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82087729183567 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246213116507 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨58, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82087729183567 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246213116507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_59 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82054158733361 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246217144771 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨59, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82054158733361 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246217144771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12746_40 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82695973447603 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246019842861 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨40, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82695973447603 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246019842861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_41 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (40362296399 / 48828125000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246023831463 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨41, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (40362296399 / 48828125000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246023831463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_42 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82628016196259 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123013901973 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨42, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82628016196259 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123013901973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_43 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82594072931267 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246031818227 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨43, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82594072931267 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246031818227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_44 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20640038300167 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246035814411 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨44, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20640038300167 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246035814411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_45 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41263128487553 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (280754981253 / 12500000000000 : ℝ))
      (E := (cell12746 ⟨45, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41263128487553 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (280754981253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_46 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (10311548028171 / 12500000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561510966173 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨46, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (10311548028171 / 12500000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561510966173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_47 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82458534922391 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123023928321 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨47, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82458534922391 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123023928321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_48 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82424709037257 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561512970707 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨48, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82424709037257 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561512970707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_49 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82390906541193 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246055882159 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨49, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82390906541193 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246055882159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_50 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82357127405569 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246059852223 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨50, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82357127405569 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246059852223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_51 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41161685800951 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449212781683 / 20000000000000 : ℝ))
      (E := (cell12746 ⟨51, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41161685800951 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449212781683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_52 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82289639101847 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (112303393547 / 5000000000000 : ℝ))
      (E := (cell12746 ⟨52, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82289639101847 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (112303393547 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_53 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (16451185975441 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561517978463 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨53, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (16451185975441 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561517978463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_54 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (16444448779983 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123037957937 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨54, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (16444448779983 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123037957937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_55 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82188581142057 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123039966323 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨55, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82188581142057 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123039966323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_56 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (1643098831517 / 2000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561520975359 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨56, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (1643098831517 / 2000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561520975359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_57 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82121325173653 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123043968333 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨57, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82121325173653 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123043968333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_58 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82087731907961 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123045958019 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨58, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82087731907961 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123045958019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_59 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (5128385109463 / 6250000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123047976827 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨59, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (5128385109463 / 6250000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1123047976827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12747_40 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82695970817523 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245898646511 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨40, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82695970817523 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245898646511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_41 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (1653239613921 / 2000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245902632191 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨41, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (1653239613921 / 2000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245902632191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_42 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (2065700354193 / 2500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122953330621 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨42, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (2065700354193 / 2500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122953330621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_43 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20648517800719 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280738834251 / 12500000000000 : ℝ))
      (E := (cell12747 ⟨43, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20648517800719 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280738834251 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_44 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20640037943003 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449182933873 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨44, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20640037943003 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449182933873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_45 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20631563961443 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561479661493 / 25000000000000 : ℝ))
      (E := (cell12747 ⟨45, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20631563961443 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561479661493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_46 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (644471745273 / 781250000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122961330583 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨46, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (644471745273 / 781250000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122961330583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_47 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (16491706878093 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245926654331 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨47, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (16491706878093 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245926654331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_48 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82424708803419 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245930682419 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨48, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82424708803419 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245930682419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_49 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10298863325629 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122967342169 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨49, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10298863325629 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122967342169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_50 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41178563883339 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245938716661 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨50, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41178563883339 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245938716661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_51 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (8232337225987 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (89837708713 / 4000000000000 : ℝ))
      (E := (cell12747 ⟨51, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (8232337225987 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (89837708713 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_52 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20572410014067 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (35092916953 / 1562500000000 : ℝ))
      (E := (cell12747 ⟨52, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20572410014067 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (35092916953 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_53 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82255931127671 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224595073323 / 10000000000000 : ℝ))
      (E := (cell12747 ⟨53, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82255931127671 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224595073323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_54 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82222245446019 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245954741261 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨54, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82222245446019 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245954741261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_55 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41094291491697 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245958705619 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨55, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41094291491697 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245958705619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_56 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (16430988742403 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245962740887 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨56, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (16430988742403 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245962740887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_57 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41060663802121 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122983362509 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨57, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41060663802121 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122983362509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_58 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (8208773463257 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (89838830891 / 4000000000000 : ℝ))
      (E := (cell12747 ⟨58, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (8208773463257 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (89838830891 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_59 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82054164769633 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245974760107 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨59, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82054164769633 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245974760107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12748_40 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (5168498011769 / 6250000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (112288875289 / 5000000000000 : ℝ))
      (E := (cell12748 ⟨40, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (5168498011769 / 6250000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (112288875289 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_41 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20665494591943 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245781488601 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨41, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20665494591943 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245781488601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_42 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (1291062689687 / 1562500000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245785515483 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨42, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (1291062689687 / 1562500000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245785515483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_43 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82594069475237 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245789526769 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨43, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82594069475237 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245789526769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_44 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10320018793009 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280724190167 / 12500000000000 : ℝ))
      (E := (cell12748 ⟨44, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10320018793009 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280724190167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_45 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82526254717117 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122898748921 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨45, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82526254717117 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122898748921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_46 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82492382565163 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280725189203 / 12500000000000 : ℝ))
      (E := (cell12748 ⟨46, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82492382565163 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280725189203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_47 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82458533859147 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245805508063 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨47, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82458533859147 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245805508063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_48 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10303088571269 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122904769057 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨48, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10303088571269 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122904769057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_49 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82390906669407 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245813542681 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨49, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82390906669407 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245813542681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_50 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (16471425625657 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122908789169 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨50, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (16471425625657 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122908789169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_51 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41161686459151 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (14036384897 / 625000000000 : ℝ))
      (E := (cell12748 ⟨51, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41161686459151 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (14036384897 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_52 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20572410252779 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245825555389 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨52, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20572410252779 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245825555389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_53 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (2570497886829 / 3125000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561457387489 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨53, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (2570497886829 / 3125000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561457387489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_54 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (513889043703 / 625000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (17545574719 / 781250000000 : ℝ))
      (E := (cell12748 ⟨54, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (513889043703 / 625000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (17545574719 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_55 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20547146206263 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122918797111 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨55, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20547146206263 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122918797111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_56 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41077472924233 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245841577793 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨56, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41077472924233 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245841577793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_57 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (2053033250877 / 2500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449169114003 / 20000000000000 : ℝ))
      (E := (cell12748 ⟨57, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (2053033250877 / 2500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449169114003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_58 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82087737357393 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122924813021 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨58, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82087737357393 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122924813021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_59 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41027083894019 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245853623323 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨59, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41027083894019 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245853623323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12749_40 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (10336995694993 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245656361921 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨40, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (10336995694993 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245656361921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_41 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41330988020159 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245660400693 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨41, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41330988020159 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245660400693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_42 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (20657002528251 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561416091667 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨42, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (20657002528251 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561416091667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_43 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82594067748349 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245668376511 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨43, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82594067748349 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245668376511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_44 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82560148916847 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245672429171 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨44, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82560148916847 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245672429171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_45 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82526253589141 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122838202819 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨45, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82526253589141 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122838202819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_46 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (3299695269441 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561420105517 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨46, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (3299695269441 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561420105517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_47 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16491706665687 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245684417843 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨47, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16491706665687 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245684417843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_48 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (5151544271091 / 6250000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449137689983 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨48, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (5151544271091 / 6250000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449137689983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_49 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82390906734317 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245692457191 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨49, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82390906734317 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245692457191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_50 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (10294641061299 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449139287451 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨50, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (10294641061299 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449139287451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_51 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82323373577197 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561425111623 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨51, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82323373577197 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561425111623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_52 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (10286205245799 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (22457044231 / 1000000000000 : ℝ))
      (E := (cell12749 ⟨52, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (10286205245799 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (22457044231 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_53 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41127966814889 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122854241073 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨53, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41127966814889 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122854241073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_54 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82222248539297 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (224571244327 / 10000000000000 : ℝ))
      (E := (cell12749 ⟨54, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82222248539297 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (224571244327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_55 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82188586667031 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280714560031 / 12500000000000 : ℝ))
      (E := (cell12749 ⟨55, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82188586667031 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280714560031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_56 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82154947985201 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280715058911 / 12500000000000 : ℝ))
      (E := (cell12749 ⟨56, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82154947985201 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280715058911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_57 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82121332466169 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122862235829 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨57, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82121332466169 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122862235829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_58 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82087740082431 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (112286423867 / 5000000000000 : ℝ))
      (E := (cell12749 ⟨58, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82087740082431 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (112286423867 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_59 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41027085403311 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245732484107 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨59, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41027085403311 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245732484107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

end BstLean.Part268
