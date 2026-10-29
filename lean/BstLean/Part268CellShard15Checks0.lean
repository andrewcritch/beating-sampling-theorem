import BstLean.Part268CellShard15Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12725_0 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (8407561292849 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124205976793 / 50000000000000 : ℝ))
      (E := (cell12725 ⟨0, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (8407561292849 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124205976793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_1 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (84040645919633 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562103990687 / 25000000000000 : ℝ))
      (E := (cell12725 ⟨1, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (84040645919633 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562103990687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_2 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (10500712979219 / 12500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248419958549 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨2, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (10500712979219 / 12500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248419958549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_3 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83970786634371 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281053000961 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨3, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83970786634371 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281053000961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_4 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (16787178857041 / 20000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449685600597 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨4, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (16787178857041 / 20000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449685600597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_5 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (1048762834377 / 1250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (70263498521 / 3125000000000 : ℝ))
      (E := (cell12725 ⟨5, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (1048762834377 / 1250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (70263498521 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_6 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20966545998333 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248435980633 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨6, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20966545998333 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248435980633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_7 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41915682989503 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124219989389 / 50000000000000 : ℝ))
      (E := (cell12725 ⟨7, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41915682989503 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124219989389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_8 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41898286335827 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248443954573 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨8, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41898286335827 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248443954573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_9 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20940451008983 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248447973259 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨9, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20940451008983 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248447973259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_10 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20931765009171 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (89938079353 / 4000000000000 : ℝ))
      (E := (cell12725 ⟨10, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20931765009171 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (89938079353 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_11 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (16738468127787 / 20000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248455992983 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨11, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (16738468127787 / 20000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248455992983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_12 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41828822903947 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2810575009 / 125000000000 : ℝ))
      (E := (cell12725 ⟨12, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41828822903947 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2810575009 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_13 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (1672459510179 / 2000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140528998411 / 6250000000000 : ℝ))
      (E := (cell12725 ⟨13, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (1672459510179 / 2000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (140528998411 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_14 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83588329707673 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248467959151 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨14, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83588329707673 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248467959151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_15 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83553708369811 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (44969439333 / 2000000000000 : ℝ))
      (E := (cell12725 ⟨15, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83553708369811 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (44969439333 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_16 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (8351911146129 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124238001277 / 50000000000000 : ℝ))
      (E := (cell12725 ⟨16, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (8351911146129 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124238001277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_17 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41742269474107 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (35132500217 / 1562500000000 : ℝ))
      (E := (cell12725 ⟨17, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41742269474107 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (35132500217 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_18 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83449990796859 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281060500697 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨18, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83449990796859 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281060500697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_19 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83415466973679 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248487982301 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨19, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83415466973679 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248487982301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12726_0 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (2627362433121 / 3125000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248290102709 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨0, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (2627362433121 / 3125000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248290102709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_1 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (21010157792523 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562073534267 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨1, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (21010157792523 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562073534267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_2 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (42002844701419 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124149050489 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨2, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (42002844701419 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124149050489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_3 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83970772521633 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281037764869 / 12500000000000 : ℝ))
      (E := (cell12726 ⟨3, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83970772521633 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281037764869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_4 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41967940245097 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124153070857 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨4, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41967940245097 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124153070857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_5 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83901013272427 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248310119637 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨5, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83901013272427 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248310119637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_6 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83866170832431 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248314118649 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨6, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83866170832431 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248314118649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_7 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (8383135313449 / 10000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449663617713 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨7, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (8383135313449 / 10000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449663617713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_8 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83796560143077 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248322094853 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨8, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83796560143077 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248322094853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_9 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83761791822851 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124163072399 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨9, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83761791822851 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124163072399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_10 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (16745409627731 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248330129341 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨10, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (16745409627731 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248330129341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_11 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20923082263879 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248334113193 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨11, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20923082263879 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248334113193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_12 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83657634538643 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248338102821 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨12, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83657634538643 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248338102821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_13 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83622964553427 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (56208552611 / 2500000000000 : ℝ))
      (E := (cell12726 ⟨13, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83622964553427 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (56208552611 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_14 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83588319065437 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124173062011 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨14, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83588319065437 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124173062011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_15 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10444212255053 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248350109123 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨15, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10444212255053 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248350109123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_16 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41759550722157 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248354123343 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨16, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41759550722157 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248354123343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_17 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20871132310803 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281044764213 / 12500000000000 : ℝ))
      (E := (cell12726 ⟨17, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20871132310803 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281044764213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_18 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (16689996280679 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124181071683 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨18, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (16689996280679 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124181071683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_19 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41707728945659 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248366158821 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨19, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41707728945659 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248366158821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12727_0 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (672604662349 / 800000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281021038119 / 12500000000000 : ℝ))
      (E := (cell12727 ⟨0, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (672604662349 / 800000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281021038119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_1 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (21010154105721 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449634461347 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨1, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (21010154105721 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449634461347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_2 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (84005674974217 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124088148327 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨2, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (84005674974217 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124088148327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_3 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (1679415168223 / 2000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124090141763 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨3, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (1679415168223 / 2000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124090141763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_4 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83935866697399 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224818427591 / 10000000000000 : ℝ))
      (E := (cell12727 ⟨4, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83935866697399 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224818427591 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_5 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83900999796873 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248188282107 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨5, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83900999796873 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248188282107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_6 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83866157673669 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248192310163 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨6, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83866157673669 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248192310163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_7 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (3353253611683 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248196309891 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨7, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (3353253611683 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248196309891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_8 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20949136904141 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248200288757 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨8, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20949136904141 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248200288757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_9 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (16752355922359 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281025539 / 12500000000 : ℝ))
      (E := (cell12727 ⟨9, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (16752355922359 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281025539 / 12500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_10 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83727036242613 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124104135279 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨10, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83727036242613 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124104135279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_11 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (16738463494809 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449642457443 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨11, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (16738463494809 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449642457443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_12 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41828811635651 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224821631041 / 10000000000000 : ℝ))
      (E := (cell12727 ⟨12, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41828811635651 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224821631041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_13 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (3344918143991 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124110144121 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨13, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (3344918143991 / 4000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124110144121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_14 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (16717661685007 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248224284751 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨14, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (16717661685007 / 20000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248224284751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_15 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83553687712833 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124114152829 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨15, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83553687712833 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124114152829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_16 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (10439886428637 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449646459651 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨16, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (10439886428637 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449646459651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_17 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (8348451953993 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248236325917 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨17, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (8348451953993 / 10000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248236325917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_18 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41724986005807 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (140515017323 / 6250000000000 : ℝ))
      (E := (cell12727 ⟨18, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41724986005807 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (140515017323 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_19 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41707724405301 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449648854627 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨19, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41707724405301 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449648854627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12728_0 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (21018891932437 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449609300501 / 20000000000000 : ℝ))
      (E := (cell12728 ⟨0, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (21018891932437 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449609300501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_1 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (84040601678007 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248050471751 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨1, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (84040601678007 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248050471751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_2 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (84005660547889 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248054487719 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨2, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (84005660547889 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248054487719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_3 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (83970744302921 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248058501411 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨3, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (83970744302921 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248058501411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_4 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (4196792645341 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248062463479 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨4, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (4196792645341 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248062463479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_5 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (16780197264699 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449613299603 / 20000000000000 : ℝ))
      (E := (cell12728 ⟨5, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (16780197264699 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449613299603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_6 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41933072258523 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281008812153 / 12500000000000 : ℝ))
      (E := (cell12728 ⟨6, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41933072258523 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281008812153 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_7 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (83831327451761 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (89922978753 / 4000000000000 : ℝ))
      (E := (cell12728 ⟨7, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (83831327451761 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (89922978753 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_8 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (83796535092113 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124039239143 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨8, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (83796535092113 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124039239143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_9 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (83761767402763 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124041237433 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨9, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (83761767402763 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124041237433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_10 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20931756087139 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248086465527 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨10, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20931756087139 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248086465527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_11 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41846152947261 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (44961810301 / 2000000000000 : ℝ))
      (E := (cell12728 ⟨11, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41846152947261 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (44961810301 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_12 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (8365761200587 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124047256891 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨12, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (8365761200587 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124047256891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_13 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41811471323997 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124049233933 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨13, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41811471323997 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124049233933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_14 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41794148893233 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248102499481 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨14, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41794148893233 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248102499481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_15 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (83553677387037 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562026624523 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨15, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (83553677387037 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562026624523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_16 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20879770353909 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562027631823 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨16, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20879770353909 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562027631823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_17 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (2608890932449 / 3125000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281014309487 / 12500000000000 : ℝ))
      (E := (cell12728 ⟨17, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (2608890932449 / 3125000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (281014309487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_18 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (16689992524303 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449623704691 / 20000000000000 : ℝ))
      (E := (cell12728 ⟨18, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (16689992524303 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449623704691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_19 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (8341543973153 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124061250009 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨19, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (8341543973153 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124061250009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12729_0 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (84075552668241 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (280990586921 / 12500000000000 : ℝ))
      (E := (cell12729 ⟨0, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (84075552668241 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (280990586921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_1 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (42020293467731 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247928747789 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨1, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (42020293467731 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247928747789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_2 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (42002823061927 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247932732033 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨2, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (42002823061927 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247932732033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_3 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41985365098473 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89917468589 / 4000000000000 : ℝ))
      (E := (cell12729 ⟨3, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41985365098473 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89917468589 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_4 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (10491979889807 / 12500000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89917628177 / 4000000000000 : ℝ))
      (E := (cell12729 ⟨4, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (10491979889807 / 12500000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (89917628177 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_5 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (16780194570459 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (224794470943 / 10000000000000 : ℝ))
      (E := (cell12729 ⟨5, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (16780194570459 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (224794470943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_6 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41933065681281 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449589747557 / 20000000000000 : ℝ))
      (E := (cell12729 ⟨6, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41933065681281 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449589747557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_7 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41915657306773 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247952739301 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨7, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41915657306773 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247952739301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_8 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83796522569723 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1123978360721 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨8, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83796522569723 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1123978360721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_9 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41880877597877 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449592149889 / 20000000000000 : ℝ))
      (E := (cell12729 ⟨9, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41880877597877 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449592149889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_10 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (16745402491297 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247964714247 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨10, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (16745402491297 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247964714247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_11 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (16738458863389 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247968738629 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨11, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (16738458863389 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247968738629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_12 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20914400185587 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449594542587 / 20000000000000 : ℝ))
      (E := (cell12729 ⟨12, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20914400185587 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449594542587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_13 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (16724586339617 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247976701427 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨13, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (16724586339617 / 20000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247976701427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_14 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83588287149731 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247980710071 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨14, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83588287149731 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247980710071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_15 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83553667063037 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (561996186147 / 25000000000000 : ℝ))
      (E := (cell12729 ⟨15, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83553667063037 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (561996186147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_16 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83519071403933 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (561997188067 / 25000000000000 : ℝ))
      (E := (cell12729 ⟨16, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83519071403933 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (561997188067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_17 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41742250069263 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247992738273 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨17, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41742250069263 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2247992738273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_18 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83449953233097 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1123998382879 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨18, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83449953233097 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1123998382879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_19 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41707715327051 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562000180739 / 25000000000000 : ℝ))
      (E := (cell12729 ⟨19, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41707715327051 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562000180739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12730_0 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (84075537609103 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224780299917 / 10000000000000 : ℝ))
      (E := (cell12730 ⟨0, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (84075537609103 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224780299917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_1 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (84040572195247 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (35121983771 / 1562500000000 : ℝ))
      (E := (cell12730 ⟨1, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (84040572195247 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (35121983771 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_2 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (84005631702111 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247810971739 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨2, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (84005631702111 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247810971739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_3 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (10496339511653 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449562996271 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨3, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (10496339511653 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449562996271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_4 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83935825332307 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561954749687 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨4, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83935825332307 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561954749687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_5 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83900959383271 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123911487143 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨5, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83900959383271 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123911487143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_6 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (10483264776277 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (280978371737 / 12500000000000 : ℝ))
      (E := (cell12730 ⟨6, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (10483264776277 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (280978371737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_7 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (10478912722179 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449566201073 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨7, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (10478912722179 / 12500000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449566201073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_8 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (16759302009879 / 20000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247835018227 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨8, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (16759302009879 / 20000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247835018227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_9 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (5235108936923 / 6250000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561959754923 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨9, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (5235108936923 / 6250000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561959754923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_10 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41863500283199 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123921508361 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨10, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41863500283199 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123921508361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_11 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (16738456548263 / 20000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (89913880641 / 4000000000000 : ℝ))
      (E := (cell12730 ⟨11, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (16738456548263 / 20000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (89913880641 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_12 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83657589480733 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247851024063 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨12, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83657589480733 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247851024063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_13 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41811460375023 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247854988931 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨13, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41811460375023 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247854988931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_14 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (20897069128707 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449571794933 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨14, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (20897069128707 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449571794933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_15 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83553656740831 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247862986987 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨15, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83553656740831 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247862986987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_16 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83519061393987 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2195182591 / 97656250000 : ℝ))
      (E := (cell12730 ⟨16, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83519061393987 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2195182591 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_17 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83484490440403 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247870996629 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨17, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83484490440403 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247870996629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_18 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83449943846361 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123937502039 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨18, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83449943846361 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123937502039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_19 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41707710789159 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247879000209 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨19, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41707710789159 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247879000209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12731_0 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (42037761276167 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561920324571 / 25000000000000 : ℝ))
      (E := (cell12731 ⟨0, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (42037761276167 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561920324571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_1 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (42020278728681 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247685285923 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨1, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (42020278728681 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247685285923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_2 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (84005617282659 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449537852939 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨2, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (84005617282659 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449537852939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_3 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20992675497939 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247693301297 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨3, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20992675497939 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247693301297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_4 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83935811548373 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112384864427 / 5000000000000 : ℝ))
      (E := (cell12731 ⟨4, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83935811548373 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112384864427 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_5 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41950472958211 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247701292583 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨5, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41950472958211 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247701292583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_6 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83866105060007 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224770526351 / 10000000000000 : ℝ))
      (E := (cell12731 ⟨6, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83866105060007 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (224770526351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_7 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (10478911117927 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123854633509 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨7, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (10478911117927 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123854633509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_8 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83796497531127 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247713310639 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨8, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83796497531127 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247713310639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_9 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16752346157561 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449543457121 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨9, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16752346157561 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449543457121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_10 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (10465873584787 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247721314901 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨10, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (10465873584787 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247721314901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_11 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (5230766947977 / 6250000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449545057833 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨11, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (5230766947977 / 6250000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449545057833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_12 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20914394555257 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247729272879 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨12, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20914394555257 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247729272879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_13 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83622909803877 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247733272257 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨13, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83622909803877 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247733272257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_14 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83588265881757 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123868646631 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨14, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83588265881757 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123868646631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_15 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83553646420419 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247741283451 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨15, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83553646420419 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247741283451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_16 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83519051385797 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449549061283 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨16, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83519051385797 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449549061283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_17 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41742240371999 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (89909972367 / 4000000000000 : ℝ))
      (E := (cell12731 ⟨17, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41742240371999 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (89909972367 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_18 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16689986892261 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (44955065933 / 2000000000000 : ℝ))
      (E := (cell12731 ⟨18, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16689986892261 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (44955065933 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_19 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83415412504177 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (89910293271 / 4000000000000 : ℝ))
      (E := (cell12731 ⟨19, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83415412504177 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (89910293271 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12732_0 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (42037753748967 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561889912631 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨0, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (42037753748967 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561889912631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_1 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (42020271360903 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (70236362683 / 3125000000000 : ℝ))
      (E := (cell12732 ⟨1, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (42020271360903 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (70236362683 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_2 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (42002801432749 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123783805453 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨2, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (42002801432749 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123783805453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_3 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83970687892539 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123785808337 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨3, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83970687892539 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123785808337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_4 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20983949441663 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247575631713 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨4, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20983949441663 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247575631713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_5 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83900932451749 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224757960639 / 10000000000000 : ℝ))
      (E := (cell12732 ⟨5, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83900932451749 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224757960639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_6 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (16773218382387 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561895901657 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨6, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (16773218382387 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561895901657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_7 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83831276111499 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449517528043 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨7, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83831276111499 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449517528043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_8 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (2094912125373 / 2500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247591598681 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨8, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (2094912125373 / 2500000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247591598681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_9 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83761718586863 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561898901303 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨9, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83761718586863 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561898901303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_10 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83726976792177 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224759960879 / 10000000000000 : ℝ))
      (E := (cell12732 ⟨10, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83726976792177 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224759960879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_11 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41846129797947 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561900904031 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨11, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41846129797947 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561900904031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_12 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83657566963229 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247607633671 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨12, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83657566963229 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247607633671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_13 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41811449429789 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123805804763 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨13, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41811449429789 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123805804763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_14 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41794127625259 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247615607723 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨14, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41794127625259 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247615607723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_15 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41776818050901 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123809816991 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨15, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41776818050901 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123809816991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_16 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83519041379363 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561905908897 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨16, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83519041379363 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561905908897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_17 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83484471049311 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123813808851 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨17, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83484471049311 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123813808851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_18 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (8344992507793 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561907910869 / 25000000000000 : ℝ))
      (E := (cell12732 ⟨18, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (8344992507793 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (561907910869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_19 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83415403431679 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123817829699 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨19, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83415403431679 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123817829699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12733_0 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (84075492445901 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247437998081 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨0, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (84075492445901 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247437998081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_1 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (4202026399429 / 5000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (112372098949 / 5000000000000 : ℝ))
      (E := (cell12733 ⟨1, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (4202026399429 / 5000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (112372098949 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_2 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (21001397112657 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247446010371 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨2, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (21001397112657 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247446010371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_3 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41985336897787 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (280931248171 / 12500000000000 : ℝ))
      (E := (cell12733 ⟨3, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41985336897787 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (280931248171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_4 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (10491972998393 / 12500000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (56186349259 / 2500000000000 : ℝ))
      (E := (cell12733 ⟨4, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (10491972998393 / 12500000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (56186349259 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_5 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83900918989251 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123728986821 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨5, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83900918989251 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123728986821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_6 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83866078765999 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123731001627 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨6, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83866078765999 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123731001627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_7 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (1047890791021 / 1250000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449493201801 / 20000000000000 : ℝ))
      (E := (cell12733 ⟨7, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (1047890791021 / 1250000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449493201801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_8 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83796472500773 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449493999671 / 20000000000000 : ℝ))
      (E := (cell12733 ⟨8, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83796472500773 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449493999671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_9 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83761706387943 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123736989257 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨9, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83761706387943 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123736989257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_10 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41863482454021 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247478014483 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨10, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41863482454021 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247478014483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_11 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41846124013051 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247481996901 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨11, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41846124013051 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247481996901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_12 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41828777853669 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (8989943961 / 400000000000 : ℝ))
      (E := (cell12733 ⟨12, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41828777853669 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (8989943961 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_13 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (20905721979287 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (112374500037 / 5000000000000 : ℝ))
      (E := (cell12733 ⟨13, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (20905721979287 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (112374500037 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_14 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (8358824462111 / 10000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247493976191 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨14, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (8358824462111 / 10000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247493976191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_15 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83553625784977 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123748990209 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨15, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83553625784977 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123748990209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_16 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (16703806274937 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561875504723 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨16, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (16703806274937 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561875504723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_17 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83484461356343 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247505980421 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨17, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83484461356343 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247505980421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_18 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (16689983139247 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247509986323 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨18, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (16689983139247 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247509986323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_19 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83415394360823 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123756991541 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨19, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83415394360823 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123756991541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12734_0 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (16815095479247 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123658199383 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨0, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (16815095479247 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123658199383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_1 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (42020256628841 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123660202649 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨1, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (42020256628841 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123660202649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_2 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (84005574038047 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140457775327 / 6250000000000 : ℝ))
      (E := (cell12734 ⟨2, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (84005574038047 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (140457775327 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_3 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83970659700861 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112366420369 / 5000000000000 : ℝ))
      (E := (cell12734 ⟨3, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83970659700861 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112366420369 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_4 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83935770209849 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123666210147 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨4, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83935770209849 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123666210147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_5 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83900905528927 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247336394337 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨5, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83900905528927 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247336394337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_6 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83866065622199 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247340395433 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨6, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83866065622199 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247340395433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_7 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41915625226979 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247344373387 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨7, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41915625226979 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247344373387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_8 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (20949114997171 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123674196831 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨8, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (20949114997171 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123674196831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_9 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (16752338838209 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561838101377 / 25000000000000 : ℝ))
      (E := (cell12734 ⟨9, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (16752338838209 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561838101377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_10 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (8372695302589 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123678207943 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨10, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (8372695302589 / 10000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123678207943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_11 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41846118229127 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561840093357 / 25000000000000 : ℝ))
      (E := (cell12734 ⟨11, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41846118229127 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561840093357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_12 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41828772226677 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247364400711 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨12, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41828772226677 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247364400711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_13 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83622876976587 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112368419389 / 5000000000000 : ℝ))
      (E := (cell12734 ⟨13, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83622876976587 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (112368419389 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_14 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (20897058498383 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123686199333 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨14, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (20897058498383 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123686199333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_15 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41776807734973 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123688190461 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨15, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41776807734973 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123688190461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_16 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41759510685881 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247380398139 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨16, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41759510685881 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247380398139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_17 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83484451665091 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449476879467 / 20000000000000 : ℝ))
      (E := (cell12734 ⟨17, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83484451665091 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (449476879467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_18 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (4172495315811 / 5000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (35115443491 / 1562500000000 : ℝ))
      (E := (cell12734 ⟨18, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (4172495315811 / 5000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (35115443491 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_19 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83415385291609 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247392419341 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨19, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83415385291609 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247392419341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12735_0 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (10509432793617 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224719479477 / 10000000000000 : ℝ))
      (E := (cell12735 ⟨0, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (10509432793617 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224719479477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_1 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (10505062316139 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (561799706743 / 25000000000000 : ℝ))
      (E := (cell12735 ⟨1, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (10505062316139 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (561799706743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_2 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (16801111925551 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224720279549 / 10000000000000 : ℝ))
      (E := (cell12735 ⟨2, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (16801111925551 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224720279549 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_3 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41985322804199 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224720682483 / 10000000000000 : ℝ))
      (E := (cell12735 ⟨3, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41985322804199 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224720682483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_4 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83935756434767 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247210807797 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨4, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83935756434767 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247210807797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_5 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83900892070777 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247214810549 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨5, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83900892070777 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247214810549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_6 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41933026240267 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247218841121 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨6, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41933026240267 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247218841121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_7 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83831237628333 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247222849319 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨7, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83831237628333 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247222849319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_8 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (16759289495731 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123613421301 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨8, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (16759289495731 / 20000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123613421301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_9 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41880840998083 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123615414089 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨9, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41880840998083 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123615414089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_10 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (2093173528643 / 2500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247234813001 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨10, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (2093173528643 / 2500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247234813001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_11 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (1673844497847 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247238803777 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨11, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (1673844497847 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247238803777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_12 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (3346301328051 / 4000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247242806963 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨12, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (3346301328051 / 4000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247242806963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_13 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41811433018947 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247246828767 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨13, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41811433018947 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247246828767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_14 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41794111683893 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (140453176063 / 6250000000000 : ℝ))
      (E := (cell12735 ⟨14, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41794111683893 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (140453176063 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_15 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83553605156707 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123627417749 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨15, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83553605156707 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123627417749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_16 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83519011370593 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247258831521 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨16, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83519011370593 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247258831521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_17 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20871110493889 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247262810233 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨17, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20871110493889 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247262810233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_18 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20862474234471 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (70227088587 / 3125000000000 : ℝ))
      (E := (cell12735 ⟨18, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20862474234471 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (70227088587 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_19 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83415376224037 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247270851661 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨19, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83415376224037 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247270851661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12736_0 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (84075447304003 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (56176832543 / 2500000000000 : ℝ))
      (E := (cell12736 ⟨0, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (84075447304003 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (56176832543 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_1 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (84040483802869 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247077301843 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨1, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (84040483802869 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247077301843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_2 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (10500693152469 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247081296867 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨2, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (10500693152469 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247081296867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_3 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41985315759093 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (5617713239 / 250000000000 : ℝ))
      (E := (cell12736 ⟨3, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41985315759093 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (5617713239 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_4 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (10491967832737 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247089306593 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨4, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (10491967832737 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247089306593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_5 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (209752196537 / 250000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247093280207 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨5, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (209752196537 / 250000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247093280207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_6 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (16773207868201 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561774320591 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨6, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (16773207868201 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561774320591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_7 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (16766244960961 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247101262867 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨7, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (16766244960961 / 20000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247101262867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_8 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20949108742671 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (280888160897 / 12500000000000 : ℝ))
      (E := (cell12736 ⟨8, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20949108742671 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (280888160897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_9 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20940417450827 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (70222165767 / 3125000000000 : ℝ))
      (E := (cell12736 ⟨9, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20940417450827 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (70222165767 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_10 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20931732316883 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247113321923 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨10, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20931732316883 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247113321923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_11 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (8369221332839 / 10000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247117287949 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨11, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (8369221332839 / 10000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247117287949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_12 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83657521951103 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (22471212671 / 1000000000000 : ℝ))
      (E := (cell12736 ⟨12, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83657521951103 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (22471212671 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_13 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83622855101069 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123562661851 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨13, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83622855101069 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123562661851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_14 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83588212743869 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (28089116117 / 1250000000000 : ℝ))
      (E := (cell12736 ⟨14, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83588212743869 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (28089116117 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_15 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (4177679742263 / 5000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123566642991 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨15, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (4177679742263 / 5000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123566642991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_16 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83519001371179 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561784329759 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨16, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83519001371179 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561784329759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_17 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41742216143869 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247141277327 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨17, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41742216143869 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247141277327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_18 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83449887561227 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247145282167 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨18, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83449887561227 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247145282167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_19 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41707683579053 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247149280043 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨19, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41707683579053 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247149280043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12737_0 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (16815086452287 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246951803989 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨0, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (16815086452287 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246951803989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_1 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (42020234539477 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280869471509 / 12500000000000 : ℝ))
      (E := (cell12737 ⟨1, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (42020234539477 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280869471509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_2 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (42002765407019 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123479896821 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨2, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (42002765407019 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123479896821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_3 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83970617430223 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246963761809 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨3, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83970617430223 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246963761809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_4 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20983932222809 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123483900433 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨4, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20983932222809 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123483900433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_5 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20975216290249 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123485901657 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨5, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20975216290249 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123485901657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_6 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83866026203609 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123487888559 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨6, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83866026203609 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123487888559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_7 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83831211983373 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246979787967 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨7, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83831211983373 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246979787967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_8 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (8379642246477 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561745946347 / 25000000000000 : ℝ))
      (E := (cell12737 ⟨8, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (8379642246477 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561745946347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_9 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (8376165761247 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280873472073 / 12500000000000 : ℝ))
      (E := (cell12737 ⟨9, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (8376165761247 / 10000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280873472073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_10 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (3349076695653 / 4000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (35109246383 / 1562500000000 : ℝ))
      (E := (cell12737 ⟨10, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (3349076695653 / 4000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (35109246383 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_11 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41846100883187 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246995767873 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨11, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41846100883187 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2246995767873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_12 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20914377675709 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123499890561 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨12, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20914377675709 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123499890561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_13 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83622844166111 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247003814467 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨13, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83622844166111 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247003814467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_14 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83588202121781 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561751953931 / 25000000000000 : ℝ))
      (E := (cell12737 ⟨14, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83588202121781 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (561751953931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_15 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20888396133901 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247011790539 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨15, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20888396133901 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247011790539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_16 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41759495686759 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123507901249 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨16, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41759495686759 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123507901249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_17 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20871105650409 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123509899309 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨17, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20871105650409 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123509899309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_18 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83449878186247 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (224702378381 / 10000000000000 : ℝ))
      (E := (cell12737 ⟨18, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83449878186247 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (224702378381 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_19 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (16683071618763 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449405564201 / 20000000000000 : ℝ))
      (E := (cell12737 ⟨19, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (16683071618763 / 20000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449405564201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12738_0 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (5254713576327 / 6250000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (112341515079 / 5000000000000 : ℝ))
      (E := (cell12738 ⟨0, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (5254713576327 / 6250000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (112341515079 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_1 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (21010113589341 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (4493668591 / 200000000000 : ℝ))
      (E := (cell12738 ⟨1, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (21010113589341 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (4493668591 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_2 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (84005516410611 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246838343679 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨2, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (84005516410611 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246838343679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_3 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83970603344509 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246842339227 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨3, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83970603344509 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246842339227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_4 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83935715122787 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246846290619 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨4, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83935715122787 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246846290619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_5 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20975212927341 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246850321939 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨5, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20975212927341 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246850321939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_6 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20966503267087 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280856790673 / 12500000000000 : ℝ))
      (E := (cell12738 ⟨6, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20966503267087 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280856790673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_7 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83831199164037 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280857288583 / 12500000000000 : ℝ))
      (E := (cell12738 ⟨7, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83831199164037 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280857288583 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_8 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41898204980457 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561715584309 / 25000000000000 : ℝ))
      (E := (cell12738 ⟨8, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41898204980457 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (561715584309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_9 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (1675232908473 / 2000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123433151163 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨9, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (1675232908473 / 2000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123433151163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_10 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (837269055171 / 1000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246870326911 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨10, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (837269055171 / 1000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246870326911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_11 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83692190206301 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123437150811 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨11, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83692190206301 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123437150811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_12 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41828749728237 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246878349033 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨12, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41828749728237 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246878349033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_13 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (4181141661651 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280860287633 / 12500000000000 : ℝ))
      (E := (cell12738 ⟨13, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (4181141661651 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (280860287633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_14 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41794095750761 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123443168979 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨14, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41794095750761 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123443168979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_15 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (4177678711387 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246890349169 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨15, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (4177678711387 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246890349169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_16 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83518981377611 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246894340097 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨16, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83518981377611 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246894340097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_17 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (333937651669 / 400000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449379663179 / 20000000000000 : ℝ))
      (E := (cell12738 ⟨17, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (333937651669 / 400000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449379663179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_18 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41724934406473 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246902339713 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨18, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41724934406473 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246902339713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_19 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (16683069806233 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246906358031 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨19, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (16683069806233 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246906358031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12739_0 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (42037701091697 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123354426153 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨0, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (42037701091697 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123354426153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_1 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (840404396381 / 1000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246712872127 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨1, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (840404396381 / 1000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246712872127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_2 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (84005502009471 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123358444559 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨2, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (84005502009471 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123358444559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_3 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20992647315261 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (11233604271 / 500000000000 : ℝ))
      (E := (cell12739 ⟨3, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20992647315261 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (11233604271 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_4 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20983925339137 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246724891667 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨4, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20983925339137 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246724891667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_5 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83900838259903 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (35105138969 / 1562500000000 : ℝ))
      (E := (cell12739 ⟨5, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83900838259903 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (35105138969 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_6 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (4193299996761 / 5000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224673286921 / 10000000000000 : ℝ))
      (E := (cell12739 ⟨6, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (4193299996761 / 5000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224673286921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_7 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16766237269359 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123368441469 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨7, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16766237269359 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123368441469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_8 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16759279491823 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123370442361 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨8, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16759279491823 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123370442361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_9 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83761633236849 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280843110221 / 12500000000000 : ℝ))
      (E := (cell12739 ⟨9, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83761633236849 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (280843110221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_10 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41863446822427 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123374440513 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨10, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41863446822427 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123374440513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_11 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83692178648169 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123376444599 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨11, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83692178648169 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123376444599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_12 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (5228593013251 / 6250000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246756912737 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨12, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (5228593013251 / 6250000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246756912737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_13 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20905705575449 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246760899729 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨13, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20905705575449 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246760899729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_14 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20897045220773 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449352982841 / 20000000000000 : ℝ))
      (E := (cell12739 ⟨14, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20897045220773 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449352982841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_15 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41776781960833 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246768903711 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨15, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41776781960833 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246768903711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_16 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (2609967855733 / 3125000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449354574729 / 20000000000000 : ℝ))
      (E := (cell12739 ⟨16, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (2609967855733 / 3125000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449354574729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_17 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41742201617289 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246776887373 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨17, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41742201617289 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246776887373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_18 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83449859441323 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123390445821 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨18, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83449859441323 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123390445821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_19 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16683067994031 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123392445561 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨19, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16683067994031 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123392445561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12740_0 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (84075387147919 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561646864043 / 25000000000000 : ℝ))
      (E := (cell12740 ⟨0, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (84075387147919 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561646864043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_1 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (84040424921161 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561647875489 / 25000000000000 : ℝ))
      (E := (cell12740 ⟨1, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (84040424921161 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561647875489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_2 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (42002743805309 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (112329774391 / 5000000000000 : ℝ))
      (E := (cell12740 ⟨2, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (42002743805309 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (112329774391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_3 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83970575179827 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449319896077 / 20000000000000 : ℝ))
      (E := (cell12740 ⟨3, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83970575179827 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449319896077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_4 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83935687592519 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246603488197 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨4, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83935687592519 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246603488197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_5 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41950412406307 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246607461613 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨5, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41950412406307 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246607461613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_6 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (3354639472169 / 4000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246611466551 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨6, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (3354639472169 / 4000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246611466551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_7 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (40933190201 / 48828125000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246615452811 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨7, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (40933190201 / 48828125000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246615452811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_8 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (20949096239843 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246619485849 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨8, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (20949096239843 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246619485849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_9 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41880810526033 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246623456889 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨9, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41880810526033 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246623456889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_10 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83726881774589 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246627488907 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨10, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83726881774589 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246627488907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_11 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (4184608354599 / 5000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246631472531 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨11, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (4184608354599 / 5000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246631472531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_12 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41828738484731 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246635472237 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨12, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41828738484731 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246635472237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_13 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83622811372437 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246639494231 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨13, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83622811372437 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246639494231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_14 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (8358817026649 / 10000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123321743163 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨14, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (8358817026649 / 10000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123321743163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_15 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83553553617383 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246647512329 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨15, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83553553617383 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246647512329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_16 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (16703792278211 / 20000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246651461331 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨16, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (16703792278211 / 20000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246651461331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_17 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41742196776811 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561663878263 / 25000000000000 : ℝ))
      (E := (cell12740 ⟨17, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41742196776811 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (561663878263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_18 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (5215615629461 / 6250000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449331899567 / 20000000000000 : ℝ))
      (E := (cell12740 ⟨18, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (5215615629461 / 6250000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449331899567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_19 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (1303364545481 / 1562500000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246663478539 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨19, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (1303364545481 / 1562500000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246663478539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12741_0 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (10509421514351 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123233056587 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨0, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (10509421514351 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123233056587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_1 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (84040410206547 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246470127147 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨1, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (84040410206547 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246470127147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_2 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (1680109464281 / 2000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123237040963 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨2, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (1680109464281 / 2000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123237040963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_3 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83970561100857 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246478102013 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨3, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83970561100857 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246478102013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_4 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41967836915349 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246482080209 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨4, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41967836915349 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246482080209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_5 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (10487601420937 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246486082663 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨5, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (10487601420937 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246486082663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_6 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83865973675361 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (70202816169 / 3125000000000 : ℝ))
      (E := (cell12741 ⟨6, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83865973675361 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (70202816169 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_7 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (16766232143719 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246494076263 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨7, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (16766232143719 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246494076263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_8 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20949093115421 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449299616523 / 20000000000000 : ℝ))
      (E := (cell12741 ⟨8, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20949093115421 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449299616523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_9 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83761608869301 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246502085713 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨9, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83761608869301 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246502085713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_10 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (654116171143 / 781250000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280813261563 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨10, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (654116171143 / 781250000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280813261563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_11 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83692155537733 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (224651010969 / 10000000000000 : ℝ))
      (E := (cell12741 ⟨11, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83692155537733 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (224651010969 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_12 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83657465728811 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246514085627 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨12, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83657465728811 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246514085627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_13 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (16724560088989 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561629521141 / 25000000000000 : ℝ))
      (E := (cell12741 ⟨13, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (16724560088989 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561629521141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_14 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20897039912929 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112326105623 / 5000000000000 : ℝ))
      (E := (cell12741 ⟨14, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20897039912929 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112326105623 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_15 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83553543314889 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112326305843 / 5000000000000 : ℝ))
      (E := (cell12741 ⟨15, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83553543314889 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112326305843 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_16 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (16703790280081 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123265051579 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨16, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (16703790280081 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123265051579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_17 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (4174219193719 / 5000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (7020419171 / 312500000000 : ℝ))
      (E := (cell12741 ⟨17, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (4174219193719 / 5000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (7020419171 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_18 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41724920351553 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280817262507 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨18, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41724920351553 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280817262507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_19 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20853830463263 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246542120281 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨19, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20853830463263 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246542120281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12742_0 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (84075357084059 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (35099136961 / 1562500000000 : ℝ))
      (E := (cell12742 ⟨0, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (84075357084059 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (35099136961 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_1 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (84040395494257 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280793593463 / 12500000000000 : ℝ))
      (E := (cell12742 ⟨1, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (84040395494257 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (280793593463 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_2 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (84005458819769 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123176393579 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨2, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (84005458819769 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123176393579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_3 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41985273512067 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246356776971 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨3, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41985273512067 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246356776971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_4 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41967830035543 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123180391761 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨4, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41967830035543 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123180391761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_5 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83900797924547 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246364757169 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨5, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83900797924547 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246364757169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_6 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (8386596054863 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246368763827 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨6, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (8386596054863 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246368763827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_7 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (20957786976909 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123186376647 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨7, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (20957786976909 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123186376647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_8 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (20949089991513 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123188395513 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨8, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (20949089991513 / 25000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123188395513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_9 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83761596688553 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123190384121 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨9, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83761596688553 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123190384121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_10 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83726858039997 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224638474987 / 10000000000000 : ℝ))
      (E := (cell12742 ⟨10, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83726858039997 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224638474987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_11 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41846071992713 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246388742609 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨11, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41846071992713 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246388742609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_12 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (5228590905629 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224639275291 / 10000000000000 : ℝ))
      (E := (cell12742 ⟨12, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (5228590905629 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224639275291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_13 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83622789519317 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246396786973 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨13, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83622789519317 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246396786973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_14 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83588149038769 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246400792613 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨14, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83588149038769 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246400792613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_15 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (16710706602837 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224640477547 / 10000000000000 : ℝ))
      (E := (cell12742 ⟨15, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (16710706602837 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (224640477547 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_16 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41759470705753 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246408799127 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨16, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41759470705753 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246408799127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_17 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83484374196851 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246412752381 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨17, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83484374196851 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246412752381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_18 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83449831336513 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123208378271 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨18, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83449831336513 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123208378271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_19 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83415312796959 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246420758091 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨19, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83415312796959 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246420758091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12743_0 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (10509417756959 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (17548620867 / 781250000000 : ℝ))
      (E := (cell12743 ⟨0, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (10509417756959 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (17548620867 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_1 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (8404038078429 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449245495861 / 20000000000000 : ℝ))
      (E := (cell12743 ⟨1, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (8404038078429 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (449245495861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_2 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (21001361106943 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246231429937 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨2, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (21001361106943 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246231429937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_3 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41985266474829 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123117723687 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨3, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41985266474829 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123117723687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_4 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41967823156841 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246239482321 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨4, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41967823156841 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246239482321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_5 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (10487598060471 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (701951071 / 31250000000 : ℝ))
      (E := (cell12743 ⟨5, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (10487598060471 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (701951071 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_6 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (8386594742403 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123123731883 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨6, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (8386594742403 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123123731883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_7 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83831135098769 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246251483909 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨7, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83831135098769 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246251483909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_8 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (3351853898899 / 4000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123127718539 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨8, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (3351853898899 / 4000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123127718539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_9 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41880792254911 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123129723227 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨9, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41880792254911 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123129723227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_10 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83726846175669 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123131730503 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨10, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83726846175669 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123131730503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_11 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (4184606621753 / 5000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280783435929 / 12500000000000 : ℝ))
      (E := (cell12743 ⟨11, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (4184606621753 / 5000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280783435929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_12 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83657443253219 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246271474087 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨12, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83657443253219 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246271474087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_13 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83622778595553 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112313774261 / 5000000000000 : ℝ))
      (E := (cell12743 ⟨13, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83622778595553 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (112313774261 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_14 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83588138427649 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123139734321 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨14, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83588138427649 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123139734321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_15 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (8355352271527 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (14039271801 / 625000000000 : ℝ))
      (E := (cell12743 ⟨15, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (8355352271527 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (14039271801 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_16 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83518931424359 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246287491049 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨16, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83518931424359 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246287491049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_17 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20871091130259 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123145741229 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨17, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20871091130259 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123145741229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_18 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16689964394319 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (70196733353 / 3125000000000 : ℝ))
      (E := (cell12743 ⟨18, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16689964394319 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (70196733353 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_19 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (10426912967813 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246299450231 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨19, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (10426912967813 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246299450231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12744_0 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (84075327029647 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89844086871 / 4000000000000 : ℝ))
      (E := (cell12744 ⟨0, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (84075327029647 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89844086871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_1 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (42020183038323 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246106206273 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨1, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (42020183038323 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246106206273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_2 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (84005430038059 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123055091923 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨2, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (84005430038059 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123055091923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_3 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20992629719357 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561528542777 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨3, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20992629719357 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561528542777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_4 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41967816279243 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561529544151 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨4, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41967816279243 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561529544151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_5 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83900771045159 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246122208617 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨5, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83900771045159 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246122208617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_6 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83865934301561 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561531539817 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨6, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83865934301561 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561531539817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_7 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (16766224458399 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123065105063 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨7, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (16766224458399 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123065105063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_8 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (10474541872619 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280766774347 / 12500000000000 : ℝ))
      (E := (cell12744 ⟨8, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (10474541872619 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280766774347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_9 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41880786166553 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561534544593 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨9, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41880786166553 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561534544593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_10 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83726834313319 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123071083931 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨10, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83726834313319 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123071083931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_11 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83692120886633 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246146169943 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨11, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83692120886633 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246146169943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_12 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20914358004569 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246150191063 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨12, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20914358004569 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246150191063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_13 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41811383836827 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280769272413 / 12500000000000 : ℝ))
      (E := (cell12744 ⟨13, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41811383836827 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280769272413 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_14 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41794063909177 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246158198691 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨14, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41794063909177 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246158198691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_15 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83553512418143 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123081098383 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨15, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83553512418143 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123081098383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_16 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83518921438963 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89846647157 / 4000000000000 : ℝ))
      (E := (cell12744 ⟨16, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83518921438963 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89846647157 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_17 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41742177423467 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (140385638033 / 6250000000000 : ℝ))
      (E := (cell12744 ⟨17, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41742177423467 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (140385638033 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_18 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83449812608353 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (3509647147 / 156250000000 : ℝ))
      (E := (cell12744 ⟨18, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83449812608353 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (3509647147 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_19 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83415294689687 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246178196699 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨19, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83415294689687 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246178196699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12745_0 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (84075312005983 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1122990462859 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨0, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (84075312005983 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1122990462859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_1 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (3361614054853 / 4000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224598492861 / 10000000000000 : ℝ))
      (E := (cell12745 ⟨1, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (3361614054853 / 4000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224598492861 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_2 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (8400541565063 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561497233291 / 25000000000000 : ℝ))
      (E := (cell12745 ⟨2, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (8400541565063 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561497233291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_3 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83970504807443 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (140374559261 / 6250000000000 : ℝ))
      (E := (cell12745 ⟨3, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83970504807443 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (140374559261 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_4 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (10491952350687 / 12500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561499231071 / 25000000000000 : ℝ))
      (E := (cell12745 ⟨4, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (10491952350687 / 12500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561499231071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_5 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41950378804359 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246000927631 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨5, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41950378804359 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246000927631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_6 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41932960590611 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (280750620781 / 12500000000000 : ℝ))
      (E := (cell12745 ⟨6, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41932960590611 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (280750620781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_7 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41915554743657 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561502232987 / 25000000000000 : ℝ))
      (E := (cell12745 ⟨7, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41915554743657 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (561502232987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_8 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83796322491483 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123006474059 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨8, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83796322491483 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123006474059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_9 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83761560158407 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246016963999 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨9, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83761560158407 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246016963999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_10 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41863411226473 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224602092849 / 10000000000000 : ℝ))
      (E := (cell12745 ⟨10, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41863411226473 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224602092849 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_11 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83692109340147 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246024964359 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨11, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83692109340147 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246024964359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_12 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (16731484157047 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449205792387 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨12, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (16731484157047 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449205792387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_13 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83622756753619 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449206585469 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨13, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83622756753619 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449206585469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_14 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41794058605443 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246036924617 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨14, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41794058605443 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246036924617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_15 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (20888375530701 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (70188779983 / 3125000000000 : ℝ))
      (E := (cell12745 ⟨15, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (20888375530701 / 25000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (70188779983 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_16 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83518911455317 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449208995827 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨16, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83518911455317 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449208995827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_17 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (16696869034909 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (70189029081 / 3125000000000 : ℝ))
      (E := (cell12745 ⟨17, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (16696869034909 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (70189029081 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_18 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (16689960649357 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449210587027 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨18, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (16689960649357 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449210587027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_19 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83415285638507 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (56151423481 / 2500000000000 : ℝ))
      (E := (cell12745 ⟨19, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83415285638507 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (56151423481 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12746_0 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (84075296984679 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245859732807 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨0, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (84075296984679 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245859732807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_1 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (3361613466733 / 4000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449172740831 / 20000000000000 : ℝ))
      (E := (cell12746 ⟨1, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (3361613466733 / 4000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449172740831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_2 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (16801080253097 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245867735751 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨2, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (16801080253097 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245867735751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_3 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41985245369851 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245871720693 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨3, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41985245369851 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245871720693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_4 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83935605054713 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (28073446567 / 1250000000000 : ℝ))
      (E := (cell12746 ⟨4, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83935605054713 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (28073446567 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_5 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20975186043611 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449175940021 / 20000000000000 : ℝ))
      (E := (cell12746 ⟨5, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20975186043611 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449175940021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_6 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83865908063013 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122941855419 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨6, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83865908063013 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122941855419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_7 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83831096684723 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561471926839 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨7, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83831096684723 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561471926839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_8 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83796310004067 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561472938777 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨8, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83796310004067 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561472938777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_9 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41880773992861 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245895745311 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨9, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41880773992861 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245895745311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_10 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83726810594551 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245899742889 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨10, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83726810594551 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245899742889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_11 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83692097795599 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122951877269 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨11, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83692097795599 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122951877269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_12 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (16731481910819 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (70184616519 / 3125000000000 : ℝ))
      (E := (cell12746 ⟨12, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (16731481910819 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (70184616519 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_13 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41811372917723 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245911729347 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨13, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41811372917723 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245911729347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_14 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83588106605243 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245915762707 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨14, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83588106605243 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245915762707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_15 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83553491829253 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245919718061 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨15, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83553491829253 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245919718061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_16 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83518901473421 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245923717111 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨16, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83518901473421 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245923717111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_17 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20871083875967 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561481941269 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨17, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20871083875967 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561481941269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_18 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20862448471723 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122965875229 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨18, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20862448471723 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122965875229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_19 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (16683055317793 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (224593573611 / 10000000000000 : ℝ))
      (E := (cell12746 ⟨19, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (16683055317793 / 20000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (224593573611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12747_0 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (16815056393147 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561434633807 / 25000000000000 : ℝ))
      (E := (cell12747 ⟨0, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (16815056393147 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561434633807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_1 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (84040321967647 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245742532911 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨1, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (84040321967647 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245742532911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_2 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (84005386882623 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1796597227 / 80000000000 : ℝ))
      (E := (cell12747 ⟨2, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (84005386882623 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1796597227 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_3 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41985238337103 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122875273273 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨3, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41985238337103 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122875273273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_4 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10491948913267 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245754521927 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨4, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10491948913267 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245754521927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_5 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83900730742339 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245758526039 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨5, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83900730742339 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245758526039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_6 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83865894946933 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245762566909 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨6, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83865894946933 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245762566909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_7 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (1309860685691 / 1562500000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (44915330727 / 2000000000000 : ℝ))
      (E := (cell12747 ⟨7, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (1309860685691 / 1562500000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (44915330727 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_8 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (5237268594919 / 6250000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449154111549 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨8, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (5237268594919 / 6250000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449154111549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_9 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20940383953763 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224577452231 / 10000000000000 : ℝ))
      (E := (cell12747 ⟨9, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20940383953763 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224577452231 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_10 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20931699684533 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449155710603 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨10, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20931699684533 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449155710603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_11 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (8369208625299 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122891270241 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨11, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (8369208625299 / 10000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122891270241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_12 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (16731479664971 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245786549181 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨12, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (16731479664971 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245786549181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_13 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83622734919137 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224579058531 / 10000000000000 : ℝ))
      (E := (cell12747 ⟨13, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83622734919137 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224579058531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_14 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (3343523840057 / 4000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449158907707 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨14, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (3343523840057 / 4000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449158907707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_15 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83553481537489 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122899265377 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨15, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83553481537489 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122899265377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_16 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41759445746637 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122901283713 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨16, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41759445746637 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122901283713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_17 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83484325834903 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449161307469 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨17, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83484325834903 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449161307469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_18 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41724892264337 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280726320227 / 12500000000000 : ℝ))
      (E := (cell12747 ⟨18, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41724892264337 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280726320227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_19 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83415267541059 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449162917463 / 20000000000000 : ℝ))
      (E := (cell12747 ⟨19, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83415267541059 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (449162917463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12748_0 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (84075266949151 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561404347699 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨0, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (84075266949151 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561404347699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_1 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (8404030726929 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561405353719 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨1, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (8404030726929 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561405353719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_2 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (42002686251021 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245625385023 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨2, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (42002686251021 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245625385023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_3 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41985231305477 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449125885147 / 20000000000000 : ℝ))
      (E := (cell12748 ⟨3, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41985231305477 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449125885147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_4 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20983894389941 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245633371893 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨4, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20983894389941 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245633371893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_5 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (209751793281 / 250000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561409351359 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨5, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (209751793281 / 250000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561409351359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_6 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41932940916491 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561410354637 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨6, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41932940916491 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561410354637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_7 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (16766214217163 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245645418931 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨7, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (16766214217163 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245645418931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_8 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83796285035393 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (140353088377 / 6250000000000 : ℝ))
      (E := (cell12748 ⟨8, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83796285035393 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (140353088377 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_9 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83761523646397 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449130682209 / 20000000000000 : ℝ))
      (E := (cell12748 ⟨9, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83761523646397 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (449130682209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_10 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (8372678688369 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122828708457 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨10, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (8372678688369 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122828708457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_11 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83692074712319 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122830690131 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨11, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83692074712319 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122830690131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_12 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20914346774379 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561416355913 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨12, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20914346774379 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561416355913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_13 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (8362272400469 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122834718557 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨13, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (8362272400469 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122834718557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_14 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10448510674929 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245673426529 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨14, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10448510674929 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245673426529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_15 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10444183905939 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245677397531 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨15, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10444183905939 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245677397531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_16 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20879720378719 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245681413699 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨16, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20879720378719 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245681413699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_17 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83484316167649 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561421355509 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨17, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83484316167649 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561421355509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_18 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83449775172129 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245689427447 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨18, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83449775172129 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245689427447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_19 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83415258494789 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122846717297 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨19, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83415258494789 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122846717297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12749_0 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (3363010077397 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449099259903 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨0, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (3363010077397 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449099259903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_1 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (21010073143313 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245500292217 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨1, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (21010073143313 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245500292217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_2 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (2625167441367 / 3125000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245504289571 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨2, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (2625167441367 / 3125000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245504289571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_3 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16794089709989 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280688537547 / 12500000000000 : ℝ))
      (E := (cell12749 ⟨3, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16794089709989 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280688537547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_4 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83935563815597 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245512275259 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨4, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83935563815597 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245512275259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_5 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (20975175971157 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561379070091 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨5, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (20975175971157 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561379070091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_6 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83865868721159 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122760132879 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨6, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83865868721159 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122760132879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_7 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (10478882286187 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122762148561 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨7, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (10478882286187 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122762148561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_8 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41898136277067 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (140345516623 / 6250000000000 : ℝ))
      (E := (cell12749 ⟨8, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41898136277067 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (140345516623 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_9 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16752302295951 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245532295469 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨9, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16752302295951 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245532295469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_10 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83726775031223 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245536276541 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨10, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83726775031223 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245536276541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_11 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41846031586793 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (56138506847 / 2500000000000 : ℝ))
      (E := (cell12749 ⟨11, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41846031586793 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (56138506847 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_12 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (20914343968019 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245544293929 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨12, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (20914343968019 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245544293929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_13 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (10452839136513 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561387071191 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨13, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (10452839136513 / 12500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561387071191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_14 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41794037399631 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245552310407 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨14, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41794037399631 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245552310407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_15 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83553460959321 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561389079599 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨15, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83553460959321 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561389079599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_16 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83518871538227 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245560314121 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨16, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83518871538227 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245560314121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_17 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41742153251053 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122782151363 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨17, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41742153251053 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122782151363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_18 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83449765817257 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449113657823 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨18, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83449765817257 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449113657823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_19 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16683049890031 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245572277949 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨19, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16683049890031 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245572277949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

end BstLean.Part268
