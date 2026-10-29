import BstLean.Part268CellShard15Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12725_20 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (833809674453 / 1000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449698401357 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨20, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (833809674453 / 1000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449698401357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_21 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83346492178519 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248496024997 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨21, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83346492178519 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248496024997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_22 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41656020570153 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248499982573 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨22, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41656020570153 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248499982573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_23 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (416388071489 / 500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248503999871 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨23, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (416388071489 / 500000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248503999871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_24 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20810802904577 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248508022081 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨24, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20810802904577 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248508022081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_25 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41604416534653 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248511994057 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨25, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41604416534653 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248511994057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_26 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83174478618437 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449703207119 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨26, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83174478618437 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449703207119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_27 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (8314014823351 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248520032661 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨27, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (8314014823351 / 10000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248520032661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_28 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41552920941249 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (224852404621 / 10000000000000 : ℝ))
      (E := (cell12725 ⟨28, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41552920941249 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (224852404621 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_29 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (83071559533537 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (89941120803 / 4000000000000 : ℝ))
      (E := (cell12725 ⟨29, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (83071559533537 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (89941120803 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_30 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (5189831322183 / 6250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281066501849 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨30, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (5189831322183 / 6250000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281066501849 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_31 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20750766678783 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248536032227 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨31, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20750766678783 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248536032227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_32 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20742214045693 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248540015453 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨32, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20742214045693 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248540015453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_33 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20733667381657 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124272012197 / 50000000000000 : ℝ))
      (E := (cell12725 ⟨33, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20733667381657 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (1124272012197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_34 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (82900506715643 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (224854806023 / 10000000000000 : ℝ))
      (E := (cell12725 ⟨34, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (82900506715643 / 100000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (224854806023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_35 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41433183859457 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449710413057 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨35, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41433183859457 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449710413057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_36 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41416126252849 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248556040219 / 100000000000000 : ℝ))
      (E := (cell12725 ⟨36, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41416126252849 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (2248556040219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_37 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (41399080522703 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562140011037 / 25000000000000 : ℝ))
      (E := (cell12725 ⟨37, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (41399080522703 / 50000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (562140011037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_38 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20691023326901 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449712815471 / 20000000000000 : ℝ))
      (E := (cell12725 ⟨38, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20691023326901 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (449712815471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12725_39 : CellCertificate 12725 (110749180819129 / 1250000000000000 : ℝ) (412660415235207 / 250000000000000000 : ℝ) (13336243893637 / 400000000000000 : ℝ)
    (cell12725 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · norm_num [cell12725]
  · have h := gap_lower (n := 12725) (a := (20682512315503 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281071010147 / 12500000000000 : ℝ))
      (E := (cell12725 ⟨39, by decide⟩).energy) (xi := (13336243893637 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12725 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12725]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12725])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12725) (a := (20682512315503 / 25000000000000 : ℝ)) (b := (80933417217 / 50000000000000 : ℝ)) (q := (281071010147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12725])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12725]

theorem cert12726_20 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (10422619834201 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248370106229 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨20, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (10422619834201 / 12500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248370106229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_21 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41673241858531 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562093541159 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨21, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41673241858531 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562093541159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_22 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20828008247163 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124189081581 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨22, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20828008247163 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124189081581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_23 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20819401613879 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449676432763 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨23, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20819401613879 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449676432763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_24 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20810801021241 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248386170083 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨24, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20810801021241 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248386170083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_25 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83208825844473 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281048765853 / 12500000000000 : ℝ))
      (E := (cell12726 ⟨25, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83208825844473 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281048765853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_26 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (16634894340337 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248394153831 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨26, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (16634894340337 / 20000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248394153831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_27 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83140141624411 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (224839813707 / 10000000000000 : ℝ))
      (E := (cell12726 ⟨27, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83140141624411 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (224839813707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_28 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (5194114723789 / 6250000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449680427499 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨28, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (5194114723789 / 6250000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449680427499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_29 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83071553538463 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562101539357 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨29, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83071553538463 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562101539357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_30 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83037295466227 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (70262816889 / 3125000000000 : ℝ))
      (E := (cell12726 ⟨30, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83037295466227 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (70262816889 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_31 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (83003061332379 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124207073443 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨31, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (83003061332379 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124207073443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_32 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (41484425552771 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124209089189 / 50000000000000 : ℝ))
      (E := (cell12726 ⟨32, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (41484425552771 / 50000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (1124209089189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_33 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82934664754499 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449684435549 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨33, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82934664754499 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449684435549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_34 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (323830086907 / 390625000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (140526634131 / 6250000000000 : ℝ))
      (E := (cell12726 ⟨34, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (323830086907 / 390625000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (140526634131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_35 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (2071659088893 / 2500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248430201581 / 100000000000000 : ℝ))
      (E := (cell12726 ⟨35, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (2071659088893 / 2500000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (2248430201581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_36 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (4141612432317 / 5000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281054271129 / 12500000000000 : ℝ))
      (E := (cell12726 ⟨36, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (4141612432317 / 5000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (281054271129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_37 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82798157489463 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (89937526647 / 4000000000000 : ℝ))
      (E := (cell12726 ⟨37, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82798157489463 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (89937526647 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_38 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (82764090054657 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562110548323 / 25000000000000 : ℝ))
      (E := (cell12726 ⟨38, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (82764090054657 / 100000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (562110548323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12726_39 : CellCertificate 12726 (442982808604471 / 5000000000000000 : ℝ) (1650511912137707 / 1000000000000000000 : ℝ) (166689631090007 / 5000000000000000 : ℝ)
    (cell12726 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · norm_num [cell12726]
  · have h := gap_lower (n := 12726) (a := (20682511577911 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449689238343 / 20000000000000 : ℝ))
      (E := (cell12726 ⟨39, by decide⟩).energy) (xi := (166689631090007 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12726 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12726]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12726])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12726) (a := (20682511577911 / 25000000000000 : ℝ)) (b := (80926980291 / 50000000000000 : ℝ)) (q := (449689238343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12726])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12726]

theorem cert12727_20 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41690474951761 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248248318327 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨20, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41690474951761 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248248318327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_21 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41673237628587 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124126150203 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨21, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41673237628587 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124126150203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_22 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83312024838529 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248256281593 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨22, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83312024838529 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248256281593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_23 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83277598614727 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562065080991 / 25000000000000 : ℝ))
      (E := (cell12727 ⟨23, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83277598614727 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562065080991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_24 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41621598276539 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224826431433 / 10000000000000 : ℝ))
      (E := (cell12727 ⟨24, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41621598276539 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (224826431433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_25 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83208818621059 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (70258384821 / 3125000000000 : ℝ))
      (E := (cell12727 ⟨25, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83208818621059 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (70258384821 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_26 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20793616196579 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281034040851 / 12500000000000 : ℝ))
      (E := (cell12727 ⟨26, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20793616196579 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (281034040851 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_27 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83140135016657 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124138148141 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨27, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83140135016657 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124138148141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_28 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41552914640029 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248280342113 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨28, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41552914640029 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248280342113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_29 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83071547544659 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248284349709 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨29, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83071547544659 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248284349709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_30 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (83037289778759 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248288321093 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨30, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (83037289778759 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248288321093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_31 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41501527975411 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248292316597 / 100000000000000 : ℝ))
      (E := (cell12727 ⟨31, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41501527975411 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (2248292316597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_32 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82968846029473 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562074084463 / 25000000000000 : ℝ))
      (E := (cell12727 ⟨32, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82968846029473 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562074084463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_33 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41467329991747 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124150163841 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨33, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41467329991747 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124150163841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_34 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (20725124445457 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562076086451 / 25000000000000 : ℝ))
      (E := (cell12727 ⟨34, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (20725124445457 / 25000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (562076086451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_35 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (10358294924197 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124154167269 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨35, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (10358294924197 / 12500000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124154167269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_36 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (41416122393997 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124156176601 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨36, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (41416122393997 / 50000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124156176601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_37 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (2587442310453 / 3125000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (112415817181 / 5000000000000 : ℝ))
      (E := (cell12727 ⟨37, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (2587442310453 / 3125000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (112415817181 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_38 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (1655281736053 / 2000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124160182353 / 50000000000000 : ℝ))
      (E := (cell12727 ⟨38, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (1655281736053 / 2000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (1124160182353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12727_39 : CellCertificate 12727 (442968896031529 / 5000000000000000 : ℝ) (206297772966351 / 125000000000000000 : ℝ) (333352431396131 / 10000000000000000 : ℝ)
    (cell12727 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · norm_num [cell12727]
  · have h := gap_lower (n := 12727) (a := (82730043362177 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449664871559 / 20000000000000 : ℝ))
      (E := (cell12727 ⟨39, by decide⟩).energy) (xi := (333352431396131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12727 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12727]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12727])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12727) (a := (82730043362177 / 100000000000000 : ℝ)) (b := (20230136099 / 12500000000000 : ℝ)) (q := (449664871559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12727])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12727]

theorem cert12728_20 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20845235283761 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562031631629 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨20, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20845235283761 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562031631629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_21 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10418308349857 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224813049061 / 10000000000000 : ℝ))
      (E := (cell12728 ⟨21, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10418308349857 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224813049061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_22 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41656008344969 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (140508407053 / 6250000000000 : ℝ))
      (E := (cell12728 ⟨22, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41656008344969 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (140508407053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_23 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10409698846929 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248138538673 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨23, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10409698846929 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248138538673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_24 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10405398627831 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124071256599 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨24, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10405398627831 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124071256599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_25 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (16641762279813 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562036624501 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨25, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (16641762279813 / 20000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562036624501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_26 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10396807234041 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224815049611 / 10000000000000 : ℝ))
      (E := (cell12728 ⟨26, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10396807234041 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224815049611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_27 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10392516051281 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248154510301 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨27, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10392516051281 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248154510301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_28 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (51941139363 / 62500000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248158543131 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨28, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (51941139363 / 62500000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248158543131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_29 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (664572332417 / 800000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562040634607 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨29, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (664572332417 / 800000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562040634607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_30 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (20759321023131 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224816655673 / 10000000000000 : ℝ))
      (E := (cell12728 ⟨30, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (20759321023131 / 25000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (224816655673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_31 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41501525285231 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124085270679 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨31, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41501525285231 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124085270679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_32 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (41484420477281 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248174552441 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨32, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (41484420477281 / 50000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248174552441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_33 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (8293465521361 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124089266397 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨33, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (8293465521361 / 10000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124089266397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_34 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82900493316549 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248182542139 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨34, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82900493316549 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248182542139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_35 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (517914720203 / 625000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248186522793 / 100000000000000 : ℝ))
      (E := (cell12728 ⟨35, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (517914720203 / 625000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (2248186522793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_36 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (4141612046533 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124095267037 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨36, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (4141612046533 / 5000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124095267037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_37 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (10349768797563 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562048644121 / 25000000000000 : ℝ))
      (E := (cell12728 ⟨37, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (10349768797563 / 12500000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (562048644121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_38 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82764083551581 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124099266449 / 50000000000000 : ℝ))
      (E := (cell12728 ⟨38, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82764083551581 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (1124099266449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12728_39 : CellCertificate 12728 (177181994222877 / 2000000000000000 : ℝ) (825126237857661 / 500000000000000000 : ℝ) (333325604988113 / 10000000000000000 : ℝ)
    (cell12728 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · norm_num [cell12728]
  · have h := gap_lower (n := 12728) (a := (82730040413613 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449640515883 / 20000000000000 : ℝ))
      (E := (cell12728 ⟨39, by decide⟩).energy) (xi := (333325604988113 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12728 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12728]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12728])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12728) (a := (82730040413613 / 100000000000000 : ℝ)) (b := (161828219063 / 100000000000000 : ℝ)) (q := (449640515883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12728])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12728]

theorem cert12729_20 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20845233092043 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248004730799 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨20, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20845233092043 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248004730799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_21 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41673229171053 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248008735251 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨21, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41673229171053 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248008735251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_22 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41656004271439 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124006370137 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨22, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41656004271439 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124006370137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_23 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83277582937631 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248016749589 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨23, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83277582937631 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248016749589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_24 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (3329727259747 / 4000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248020766687 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨24, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (3329727259747 / 4000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248020766687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_25 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (8320880417849 / 10000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248024736419 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨25, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (8320880417849 / 10000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248024736419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_26 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41587225479861 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124014389289 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨26, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41587225479861 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124014389289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_27 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83140121805183 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124016389563 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨27, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83140121805183 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124016389563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_28 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (1662116333657 / 2000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248036740547 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨28, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (1662116333657 / 2000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248036740547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_29 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41535767780431 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562010195519 / 25000000000000 : ℝ))
      (E := (cell12729 ⟨29, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41535767780431 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (562010195519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_30 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83037278407523 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248044788841 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨30, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83037278407523 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248044788841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_31 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (83003045191297 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124024381317 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨31, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (83003045191297 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124024381317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_32 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82968835880811 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248052763579 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨32, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82968835880811 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248052763579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_33 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82934650444849 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124028396541 / 50000000000000 : ℝ))
      (E := (cell12729 ⟨33, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82934650444849 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (1124028396541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_34 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (20725122213089 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248060793709 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨34, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (20725122213089 / 25000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248060793709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_35 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82866351072433 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449612953269 / 20000000000000 : ℝ))
      (E := (cell12729 ⟨35, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82866351072433 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (449612953269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_36 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (41416118537169 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (4390759317 / 195312500000 : ℝ))
      (E := (cell12729 ⟨36, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (41416118537169 / 50000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (4390759317 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_37 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (2587442088359 / 3125000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248072806087 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨37, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (2587442088359 / 3125000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248072806087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_38 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82764080301451 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248076815273 / 100000000000000 : ℝ))
      (E := (cell12729 ⟨38, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82764080301451 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (2248076815273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12729_39 : CellCertificate 12729 (110735269295241 / 1250000000000000 : ℝ) (825061394043221 / 500000000000000000 : ℝ) (333298782954801 / 10000000000000000 : ℝ)
    (cell12729 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · norm_num [cell12729]
  · have h := gap_lower (n := 12729) (a := (82730037465951 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (44961615957 / 2000000000000 : ℝ))
      (E := (cell12729 ⟨39, by decide⟩).energy) (xi := (333298782954801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12729 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12729]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12729])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12729) (a := (82730037465951 / 100000000000000 : ℝ)) (b := (32363070279 / 20000000000000 : ℝ)) (q := (44961615957 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12729])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12729]

theorem cert12730_20 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41690461801453 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123941494729 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨20, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41690461801453 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123941494729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_21 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (3333857995477 / 4000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224788703433 / 10000000000000 : ℝ))
      (E := (cell12730 ⟨21, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (3333857995477 / 4000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224788703433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_22 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (1666240007947 / 2000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247891022199 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨22, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (1666240007947 / 2000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247891022199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_23 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83277575101323 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247895015069 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨23, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83277575101323 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247895015069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_24 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41621586983079 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (89915960657 / 4000000000000 : ℝ))
      (E := (cell12730 ⟨24, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41621586983079 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (89915960657 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_25 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41604398479667 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (28098787869 / 1250000000000 : ℝ))
      (E := (cell12730 ⟨25, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41604398479667 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (28098787869 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_26 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41587222024249 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247906998949 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨26, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41587222024249 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247906998949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_27 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83140115201463 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449582208863 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨27, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83140115201463 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449582208863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_28 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41552905193103 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247915051303 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨28, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41552905193103 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247915051303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_29 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (20767882392717 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561979755541 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨29, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (20767882392717 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561979755541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_30 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41518636361877 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247923017431 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨30, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41518636361877 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247923017431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_31 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (83003039813329 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561981759741 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨31, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (83003039813329 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561981759741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_32 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82968830808219 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123965514917 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨32, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82968830808219 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123965514917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_33 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (8293464567721 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (56198376249 / 2500000000000 : ℝ))
      (E := (cell12730 ⟨33, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (8293464567721 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (56198376249 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_34 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82900484389247 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224793904191 / 10000000000000 : ℝ))
      (E := (cell12730 ⟨34, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82900484389247 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (224793904191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_35 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41433173456717 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123971532599 / 50000000000000 : ℝ))
      (E := (cell12730 ⟨35, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41433173456717 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (1123971532599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_36 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (20708058304757 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449589412379 / 20000000000000 : ℝ))
      (E := (cell12730 ⟨36, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (20708058304757 / 25000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (449589412379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_37 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (41399071637723 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247951091113 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨37, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (41399071637723 / 50000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247951091113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_38 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (82764077052259 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561988773607 / 25000000000000 : ℝ))
      (E := (cell12730 ⟨38, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (82764077052259 / 100000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (561988773607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12730_39 : CellCertificate 12730 (885854341804691 / 10000000000000000 : ℝ) (1649993120839363 / 1000000000000000000 : ℝ) (333271965295033 / 10000000000000000 : ℝ)
    (cell12730 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · norm_num [cell12730]
  · have h := gap_lower (n := 12730) (a := (8273003451919 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247959071829 / 100000000000000 : ℝ))
      (E := (cell12730 ⟨39, by decide⟩).energy) (xi := (333271965295033 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12730 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12730]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12730])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12730) (a := (8273003451919 / 10000000000000 : ℝ)) (b := (80901242893 / 50000000000000 : ℝ)) (q := (2247959071829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12730])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12730]

theorem cert12731_20 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16676182967849 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247761302493 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨20, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16676182967849 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247761302493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_21 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (2604576294791 / 3125000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123882664771 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨21, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (2604576294791 / 3125000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123882664771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_22 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83311992253351 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280971162537 / 12500000000000 : ℝ))
      (E := (cell12731 ⟨22, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83311992253351 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280971162537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_23 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83277567266509 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561943333777 / 25000000000000 : ℝ))
      (E := (cell12731 ⟨23, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83277567266509 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561943333777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_24 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83243166440097 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449555464157 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨24, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83243166440097 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449555464157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_25 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20802197435399 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247781318907 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨25, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20802197435399 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247781318907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_26 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16634887427731 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280973166561 / 12500000000000 : ℝ))
      (E := (cell12731 ⟨26, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16634887427731 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280973166561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_27 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41570054299543 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123894652933 / 50000000000000 : ℝ))
      (E := (cell12731 ⟨27, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41570054299543 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (1123894652933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_28 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (83105804090869 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112389667923 / 5000000000000 : ℝ))
      (E := (cell12731 ⟨28, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (83105804090869 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (112389667923 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_29 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16614304716429 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247797317181 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨29, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16614304716429 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247797317181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_30 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41518633520609 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280975169941 / 12500000000000 : ℝ))
      (E := (cell12731 ⟨30, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41518633520609 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (280975169941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_31 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20750758609139 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247805311809 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨31, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20750758609139 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247805311809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_32 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16593765147357 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561952337801 / 25000000000000 : ℝ))
      (E := (cell12731 ⟨32, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16593765147357 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561952337801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_33 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (20733660227673 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449562672403 / 20000000000000 : ℝ))
      (E := (cell12731 ⟨33, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (20733660227673 / 25000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (449562672403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_34 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (10362559990903 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247817345347 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨34, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (10362559990903 / 12500000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247817345347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_35 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (41433171377741 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561955340179 / 25000000000000 : ℝ))
      (E := (cell12731 ⟨35, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (41433171377741 / 50000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (561955340179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_36 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82832229364729 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247825350189 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨36, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82832229364729 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247825350189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_37 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (82798139724379 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247829372879 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨37, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (82798139724379 / 100000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247829372879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_38 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (16552814760801 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247833370361 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨38, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (16552814760801 / 20000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247833370361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12731_39 : CellCertificate 12731 (885826533441679 / 10000000000000000 : ℝ) (824931736984639 / 500000000000000000 : ℝ) (83311288001913 / 2500000000000000 : ℝ)
    (cell12731 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · norm_num [cell12731]
  · have h := gap_lower (n := 12731) (a := (8273003157333 / 10000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247837401351 / 100000000000000 : ℝ))
      (E := (cell12731 ⟨39, by decide⟩).energy) (xi := (83311288001913 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12731 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12731]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12731])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12731) (a := (8273003157333 / 10000000000000 : ℝ)) (b := (80894811119 / 50000000000000 : ℝ)) (q := (2247837401351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12731])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12731]

theorem cert12732_20 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (8338090607719 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449527933981 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨20, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (8338090607719 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449527933981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_21 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41673216490633 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247643620889 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨21, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41673216490633 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247643620889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_22 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83311984110883 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449529526579 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨22, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83311984110883 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449529526579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_23 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83277559433187 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (14047822821 / 625000000000 : ℝ))
      (E := (cell12732 ⟨23, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83277559433187 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (14047822821 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_24 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (8324315891549 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247655679773 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨24, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (8324315891549 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247655679773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_25 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20802195631319 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247659662981 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨25, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20802195631319 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247659662981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_26 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (5198401889387 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123831831177 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨26, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (5198401889387 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123831831177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_27 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (83140101998053 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247667680673 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨27, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (83140101998053 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247667680673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_28 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41552898898419 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247671662019 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨28, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41552898898419 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247671662019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_29 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (8307151759469 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247675667133 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨29, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (8307151759469 / 10000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247675667133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_30 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41518630679957 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (280959962263 / 12500000000000 : ℝ))
      (E := (cell12732 ⟨30, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41518630679957 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (280959962263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_31 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41501514530489 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (280960462281 / 12500000000000 : ℝ))
      (E := (cell12732 ⟨31, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41501514530489 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (280960462281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_32 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82968820666509 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247687669129 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨32, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82968820666509 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247687669129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_33 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (5183414759081 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123845835331 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨33, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (5183414759081 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123845835331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_34 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (16580095093257 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (89907828161 / 4000000000000 : ℝ))
      (E := (cell12732 ⟨34, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (16580095093257 / 20000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (89907828161 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_35 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82866338598579 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123849855767 / 50000000000000 : ℝ))
      (E := (cell12732 ⟨35, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82866338598579 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (1123849855767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_36 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (82832225511441 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449540738769 / 20000000000000 : ℝ))
      (E := (cell12732 ⟨36, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (82832225511441 / 100000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (449540738769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_37 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (41399068087143 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247707710069 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨37, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (41399068087143 / 50000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247707710069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_38 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (5172754409793 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247711701779 / 100000000000000 : ℝ))
      (E := (cell12732 ⟨38, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (5172754409793 / 6250000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (2247711701779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12732_39 : CellCertificate 12732 (885798729271899 / 10000000000000000 : ℝ) (824866923735693 / 500000000000000000 : ℝ) (41652292886437 / 1250000000000000 : ℝ)
    (cell12732 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · norm_num [cell12732]
  · have h := gap_lower (n := 12732) (a := (20682507157093 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224771572769 / 10000000000000 : ℝ))
      (E := (cell12732 ⟨39, by decide⟩).energy) (xi := (41652292886437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12732 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12732]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12732])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12732) (a := (20682507157093 / 25000000000000 : ℝ)) (b := (161776760749 / 100000000000000 : ℝ)) (q := (224771572769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12732])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12732]

theorem cert12733_20 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83380897316739 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (280939754177 / 12500000000000 : ℝ))
      (E := (cell12733 ⟨20, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83380897316739 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (280939754177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_21 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (20836606132697 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123761012491 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨21, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (20836606132697 / 25000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123761012491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_22 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (16662395193989 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561881504999 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨22, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (16662395193989 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561881504999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_23 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83277551601357 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247530022177 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨23, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83277551601357 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247530022177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_24 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83243151392339 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (224753403501 / 10000000000000 : ℝ))
      (E := (cell12733 ⟨24, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83243151392339 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (224753403501 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_25 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83208775310373 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449507600669 / 20000000000000 : ℝ))
      (E := (cell12733 ⟨25, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83208775310373 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (449507600669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_26 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (8317442332311 / 10000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (224754204697 / 10000000000000 : ℝ))
      (E := (cell12733 ⟨26, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (8317442332311 / 10000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (224754204697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_27 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83140095398363 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123773025923 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨27, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83140095398363 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123773025923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_28 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (83105791504113 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561887505113 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨28, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (83105791504113 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561887505113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_29 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (10383938951063 / 12500000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247554013527 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨29, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (10383938951063 / 12500000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247554013527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_30 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41518627839921 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247558033159 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨30, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41518627839921 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247558033159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_31 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (16600604737319 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247562022667 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨31, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (16600604737319 / 20000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247562022667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_32 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82968815597391 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561891510543 / 25000000000000 : ℝ))
      (E := (cell12733 ⟨32, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82968815597391 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (561891510543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_33 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82934631381021 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247570034489 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨33, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82934631381021 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247570034489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_34 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82900471006429 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123787029667 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨34, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82900471006429 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123787029667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_35 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82866334442723 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123789029511 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨35, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82866334442723 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123789029511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_36 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82832221659163 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (70236938569 / 3125000000000 : ℝ))
      (E := (cell12733 ⟨36, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82832221659163 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (70236938569 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_37 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82798132625167 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123793022001 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨37, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82798132625167 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123793022001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_38 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (82764067310309 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123795044341 / 50000000000000 : ℝ))
      (E := (cell12733 ⟨38, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (82764067310309 / 100000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (1123795044341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12733_39 : CellCertificate 12733 (221442732323589 / 2500000000000000 : ℝ) (824802120670443 / 500000000000000000 : ℝ) (333191538545409 / 10000000000000000 : ℝ)
    (cell12733 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · norm_num [cell12733]
  · have h := gap_lower (n := 12733) (a := (41365012842157 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247594050849 / 100000000000000 : ℝ))
      (E := (cell12733 ⟨39, by decide⟩).energy) (xi := (333191538545409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12733 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12733]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12733])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12733) (a := (41365012842157 / 50000000000000 : ℝ)) (b := (80881950659 / 50000000000000 : ℝ)) (q := (2247594050849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12733])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12733]

theorem cert12734_20 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83380888557893 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (35115568641 / 1562500000000 : ℝ))
      (E := (cell12734 ⟨20, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83380888557893 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (35115568641 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_21 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (20836604020469 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561850106303 / 25000000000000 : ℝ))
      (E := (cell12734 ⟨21, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (20836604020469 / 25000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561850106303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_22 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (10413995978817 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280925550409 / 12500000000000 : ℝ))
      (E := (cell12734 ⟨22, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (10413995978817 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280925550409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_23 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83277543771019 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247408447559 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨23, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83277543771019 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247408447559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_24 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41621571935321 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (17979299559 / 800000000000 : ℝ))
      (E := (cell12734 ⟨24, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41621571935321 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (17979299559 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_25 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (10401096012111 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247416398397 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨25, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (10401096012111 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247416398397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_26 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83174416417407 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123710213957 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨26, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83174416417407 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123710213957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_27 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (16628017760003 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123712209693 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨27, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (16628017760003 / 20000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123712209693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_28 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41552892606347 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247428433757 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨28, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41552892606347 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247428433757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_29 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41535752811793 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280929051857 / 12500000000000 : ℝ))
      (E := (cell12734 ⟨29, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41535752811793 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280929051857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_30 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (83037250001001 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247436423211 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨30, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (83037250001001 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247436423211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_31 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41501509156703 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123720230341 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨31, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41501509156703 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123720230341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_32 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82968810529431 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123722235167 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨32, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82968810529431 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123722235167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_33 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41467313308933 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280931056687 / 12500000000000 : ℝ))
      (E := (cell12734 ⟨33, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41467313308933 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (280931056687 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_34 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41450233273829 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561863117471 / 25000000000000 : ℝ))
      (E := (cell12734 ⟨34, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41450233273829 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561863117471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_35 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41433165143957 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561864115453 / 25000000000000 : ℝ))
      (E := (cell12734 ⟨35, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41433165143957 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (561864115453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_36 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (10354027225987 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (224746048859 / 10000000000000 : ℝ))
      (E := (cell12734 ⟨36, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (10354027225987 / 12500000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (224746048859 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_37 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (41399064538511 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56186612301 / 2500000000000 : ℝ))
      (E := (cell12734 ⟨37, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (41399064538511 / 50000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (56186612301 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_38 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82764064064867 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123734236183 / 50000000000000 : ℝ))
      (E := (cell12734 ⟨38, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82764064064867 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (1123734236183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12734_39 : CellCertificate 12734 (110717891688507 / 1250000000000000 : ℝ) (103092165973311 / 62500000000000000 : ℝ) (41645592296029 / 1250000000000000 : ℝ)
    (cell12734 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · norm_num [cell12734]
  · have h := gap_lower (n := 12734) (a := (82730022741157 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247472488281 / 100000000000000 : ℝ))
      (E := (cell12734 ⟨39, by decide⟩).energy) (xi := (41645592296029 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12734 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12734]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12734])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12734) (a := (82730022741157 / 100000000000000 : ℝ)) (b := (80875521973 / 50000000000000 : ℝ)) (q := (2247472488281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12734])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12734]

theorem cert12735_20 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (1667617596013 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247274865297 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨20, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (1667617596013 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247274865297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_21 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83346407634531 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247278821579 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨21, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83346407634531 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247278821579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_22 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (5206997480791 / 6250000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123641420527 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨22, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (5206997480791 / 6250000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123641420527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_23 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83277535942173 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (561821717289 / 25000000000000 : ℝ))
      (E := (cell12735 ⟨23, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83277535942173 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (561821717289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_24 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (52026960219 / 62500000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (140455678187 / 6250000000000 : ℝ))
      (E := (cell12735 ⟨24, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (52026960219 / 62500000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (140455678187 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_25 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (4160438044241 / 5000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247294848139 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨25, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (4160438044241 / 5000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247294848139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_26 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20793602378271 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224729886361 / 10000000000000 : ℝ))
      (E := (cell12735 ⟨26, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20793602378271 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (224729886361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_27 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (8314008220301 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123651420869 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨27, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (8314008220301 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123651420869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_28 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (4155288946129 / 5000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247306843469 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨28, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (4155288946129 / 5000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247306843469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_29 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83071499639937 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247310871121 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨29, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83071499639937 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247310871121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_30 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83037244323391 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123657434131 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨30, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83037244323391 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123657434131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_31 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (83003012941411 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123659447609 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨31, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (83003012941411 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123659447609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_32 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (20742201365657 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247322895053 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨32, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (20742201365657 / 25000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247322895053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_33 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (10366827731979 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123663434549 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨33, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (10366827731979 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123663434549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_34 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (8290046208997 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247330877067 / 100000000000000 : ℝ))
      (E := (cell12735 ⟨34, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (8290046208997 / 10000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (2247330877067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_35 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (10358290766769 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (280916857659 / 12500000000000 : ℝ))
      (E := (cell12735 ⟨35, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (10358290766769 / 12500000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (280916857659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_36 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (41416106978819 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (89893555241 / 4000000000000 : ℝ))
      (E := (cell12735 ⟨36, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (41416106978819 / 50000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (89893555241 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_37 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (1655962510597 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (35114732471 / 1562500000000 : ℝ))
      (E := (cell12735 ⟨37, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (1655962510597 / 2000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (35114732471 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_38 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (82764060820361 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123673455769 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨38, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (82764060820361 / 100000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123673455769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12735_39 : CellCertificate 12735 (177143068382401 / 2000000000000000 : ℝ) (82467254508143 / 50000000000000000 : ℝ) (333137942558807 / 10000000000000000 : ℝ)
    (cell12735 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · norm_num [cell12735]
  · have h := gap_lower (n := 12735) (a := (827300197989 / 1000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123675461267 / 50000000000000 : ℝ))
      (E := (cell12735 ⟨39, by decide⟩).energy) (xi := (333137942558807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12735 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12735]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12735])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12735) (a := (827300197989 / 1000000000000 : ℝ)) (b := (161738188631 / 100000000000000 : ℝ)) (q := (1123675461267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12735])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12735]

theorem cert12736_20 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20845217761253 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561788333417 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨20, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20845217761253 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561788333417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_21 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83346399188751 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123578665349 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨21, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83346399188751 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123578665349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_22 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (5206996972269 / 6250000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123580666671 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨22, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (5206996972269 / 6250000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123580666671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_23 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41638764057409 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247165345321 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨23, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41638764057409 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247165345321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_24 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83243128831611 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (112358465587 / 5000000000000 : ℝ))
      (E := (cell12736 ⟨24, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83243128831611 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (112358465587 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_25 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (10401094209271 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123586647087 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨25, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (10401094209271 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123586647087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_26 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83174402610141 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561794323909 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨26, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83174402610141 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561794323909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_27 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83140075607347 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123590659453 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨27, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83140075607347 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123590659453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_28 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (8310577263377 / 10000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247185308057 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨28, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (8310577263377 / 10000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247185308057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_29 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20767873414389 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (224718932383 / 10000000000000 : ℝ))
      (E := (cell12736 ⟨29, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20767873414389 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (224718932383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_30 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20759309661753 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449438661959 / 20000000000000 : ℝ))
      (E := (cell12736 ⟨30, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20759309661753 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (449438661959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_31 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (83003007570611 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247197326273 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨31, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (83003007570611 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247197326273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_32 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41484400198491 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247201316331 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨32, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41484400198491 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247201316331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_33 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82934617094917 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561801334971 / 25000000000000 : ℝ))
      (E := (cell12736 ⟨33, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82934617094917 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (561801334971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_34 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (41450228816683 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247209339493 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨34, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (41450228816683 / 50000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247209339493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_35 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20716580495359 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247213374671 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨35, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20716580495359 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247213374671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_36 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82832210108391 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123608693741 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨36, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82832210108391 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123608693741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_37 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (20699530495913 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123610689177 / 50000000000000 : ℝ))
      (E := (cell12736 ⟨37, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (20699530495913 / 25000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (1123610689177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_38 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (82764057576793 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247225347493 / 100000000000000 : ℝ))
      (E := (cell12736 ⟨38, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (82764057576793 / 100000000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (2247225347493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12736_39 : CellCertificate 12736 (221421888626303 / 2500000000000000 : ℝ) (1649215545105739 / 1000000000000000000 : ℝ) (166555575557989 / 5000000000000000 : ℝ)
    (cell12736 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · norm_num [cell12736]
  · have h := gap_lower (n := 12736) (a := (10341252107193 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (280903669201 / 12500000000000 : ℝ))
      (E := (cell12736 ⟨39, by decide⟩).energy) (xi := (166555575557989 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12736 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12736]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12736])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12736) (a := (10341252107193 / 12500000000000 : ℝ)) (b := (161725335373 / 100000000000000 : ℝ)) (q := (280903669201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12736])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12736]

theorem cert12737_20 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (2605651946593 / 3125000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123515899071 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨20, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (2605651946593 / 3125000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123515899071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_21 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41673195372269 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123517917977 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨21, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41673195372269 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123517917977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_22 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83311943421481 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (140439988863 / 6250000000000 : ℝ))
      (E := (cell12737 ⟨22, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83311943421481 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (140439988863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_23 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41638760144477 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123521908851 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨23, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41638760144477 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123521908851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_24 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20810780328569 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123523913559 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨24, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20810780328569 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123523913559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_25 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20802186616233 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123525897451 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨25, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20802186616233 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123525897451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_26 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (2599199865893 / 3125000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247055840839 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨26, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (2599199865893 / 3125000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247055840839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_27 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41570034506513 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280882481361 / 12500000000000 : ℝ))
      (E := (cell12737 ⟨27, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41570034506513 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280882481361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_28 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41552883173133 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247063827521 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨28, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41552883173133 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247063827521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_29 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41535743838221 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123533915739 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨29, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41535743838221 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123533915739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_30 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (10379654121483 / 12500000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123535903163 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨30, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (10379654121483 / 12500000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123535903163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_31 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (83003002201003 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (224707581239 / 10000000000000 : ℝ))
      (E := (cell12737 ⟨31, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (83003002201003 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (224707581239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_32 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20742198833123 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123539925647 / 50000000000000 : ℝ))
      (E := (cell12737 ⟨32, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20742198833123 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (1123539925647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_33 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82934612335123 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247083865851 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨33, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82934612335123 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247083865851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_34 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (20725113294461 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449417571433 / 20000000000000 : ℝ))
      (E := (cell12737 ⟨34, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (20725113294461 / 25000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (449417571433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_35 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41433158914883 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247091826109 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨35, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41433158914883 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247091826109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_36 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82832206260153 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280886978999 / 12500000000000 : ℝ))
      (E := (cell12737 ⟨36, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82832206260153 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (280886978999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_37 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (41399059219213 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247099875313 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨37, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (41399059219213 / 50000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247099875313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_38 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (1034550679177 / 1250000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247103838937 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨38, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (1034550679177 / 1250000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247103838937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12737_39 : CellCertificate 12737 (442829885643341 / 5000000000000000 : ℝ) (1649086020396819 / 1000000000000000000 : ℝ) (83271091009647 / 2500000000000000 : ℝ)
    (cell12737 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · norm_num [cell12737]
  · have h := gap_lower (n := 12737) (a := (82730013917087 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247107898959 / 100000000000000 : ℝ))
      (E := (cell12737 ⟨39, by decide⟩).energy) (xi := (83271091009647 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12737 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12737]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12737])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12737) (a := (82730013917087 / 100000000000000 : ℝ)) (b := (40428121043 / 25000000000000 : ℝ)) (q := (2247107898959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12737])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12737]

theorem cert12738_20 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83380853538543 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246910317 / 100000000000 : ℝ))
      (E := (cell12738 ⟨20, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83380853538543 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246910317 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_21 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83346382301889 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246914337353 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨21, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83346382301889 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246914337353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_22 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (16662387057637 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246918364783 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨22, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (16662387057637 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246918364783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_23 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (4163875623229 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123461172327 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨23, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (4163875623229 / 5000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123461172327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_24 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83243113798393 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (35108224043 / 1562500000000 : ℝ))
      (E := (cell12738 ⟨24, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83243113798393 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (35108224043 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_25 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (10401092407139 / 12500000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123465175161 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨25, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (10401092407139 / 12500000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123465175161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_26 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (8317438880839 / 10000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246934323951 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨26, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (8317438880839 / 10000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246934323951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_27 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41570031210023 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246938379241 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨27, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41570031210023 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246938379241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_28 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (16621152012013 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449388468679 / 20000000000000 : ℝ))
      (E := (cell12738 ⟨28, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (16621152012013 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (449388468679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_29 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (16614296339319 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246946335573 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨29, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (16614296339319 / 20000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246946335573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_30 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41518613648973 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246950357859 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨30, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41518613648973 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246950357859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_31 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (83002996832589 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (70217323549 / 3125000000000 : ℝ))
      (E := (cell12738 ⟨31, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (83002996832589 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (70217323549 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_32 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82968790269159 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246958382817 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨32, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82968790269159 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246958382817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_33 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82934607576447 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123481194209 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨33, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82934607576447 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123481194209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_34 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (41450224361703 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246966371471 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨34, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (41450224361703 / 50000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246966371471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_35 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82866313679143 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123485195743 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨35, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82866313679143 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123485195743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_36 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (20708050603231 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246974390527 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨36, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (20708050603231 / 25000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246974390527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_37 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82798114894173 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246978369019 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨37, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82798114894173 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246978369019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_38 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (5172753193279 / 6250000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246982385871 / 100000000000000 : ℝ))
      (E := (cell12738 ⟨38, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (5172753193279 / 6250000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (2246982385871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12738_39 : CellCertificate 12738 (885631992255423 / 10000000000000000 : ℝ) (329791303206261 / 200000000000000000 : ℝ) (333057581325481 / 10000000000000000 : ℝ)
    (cell12738 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · norm_num [cell12738]
  · have h := gap_lower (n := 12738) (a := (82730010977529 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123493191203 / 50000000000000 : ℝ))
      (E := (cell12738 ⟨39, by decide⟩).energy) (xi := (333057581325481 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12738 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12738]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12738])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12738) (a := (82730010977529 / 100000000000000 : ℝ)) (b := (161699635027 / 100000000000000 : ℝ)) (q := (1123493191203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12738])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12738]

theorem cert12739_20 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (40713303119 / 48828125000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561697222561 / 25000000000000 : ℝ))
      (E := (cell12739 ⟨20, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (40713303119 / 48828125000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561697222561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_21 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41673186930403 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123396446599 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨21, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41673186930403 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123396446599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_22 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83311927156417 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246796903937 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨22, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83311927156417 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246796903937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_23 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (2602422020053 / 3125000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (70212528943 / 3125000000000 : ℝ))
      (E := (cell12739 ⟨23, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (2602422020053 / 3125000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (70212528943 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_24 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83243106283963 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246804905019 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨24, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83243106283963 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246804905019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_25 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83208732050707 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123404451019 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨25, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83208732050707 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123404451019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_26 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41587190954791 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123406460121 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨26, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41587190954791 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123406460121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_27 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83140055828407 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561704225991 / 25000000000000 : ℝ))
      (E := (cell12739 ⟨27, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83140055828407 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561704225991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_28 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83105753775169 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123410457073 / 50000000000000 : ℝ))
      (E := (cell12739 ⟨28, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83105753775169 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (1123410457073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_29 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16614295143603 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (22468249531 / 1000000000000 : ℝ))
      (E := (cell12739 ⟨29, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16614295143603 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (22468249531 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_30 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (83037221625257 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246828905877 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨30, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (83037221625257 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246828905877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_31 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (10375373933171 / 12500000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246832949809 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨31, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (10375373933171 / 12500000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246832949809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_32 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (41484392603491 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246836910901 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨32, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (41484392603491 / 50000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246836910901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_33 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82934602818891 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224684096617 / 10000000000000 : ℝ))
      (E := (cell12739 ⟨33, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82934602818891 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (224684096617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_34 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82900444270049 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (70213904407 / 3125000000000 : ℝ))
      (E := (cell12739 ⟨34, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82900444270049 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (70213904407 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_35 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20716577382391 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246848953539 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨35, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20716577382391 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246848953539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_36 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (16566439713341 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561713236443 / 25000000000000 : ℝ))
      (E := (cell12739 ⟨36, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (16566439713341 / 20000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (561713236443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_37 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (20699527837723 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449371395367 / 20000000000000 : ℝ))
      (E := (cell12739 ⟨37, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (20699527837723 / 25000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449371395367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_38 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82764047851703 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449372197659 / 20000000000000 : ℝ))
      (E := (cell12739 ⟨38, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82764047851703 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (449372197659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12739_39 : CellCertificate 12739 (885604217410443 / 10000000000000000 : ℝ) (329765406400881 / 200000000000000000 : ℝ) (166515401487751 / 5000000000000000 : ℝ)
    (cell12739 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · norm_num [cell12739]
  · have h := gap_lower (n := 12739) (a := (82730008038871 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246864980131 / 100000000000000 : ℝ))
      (E := (cell12739 ⟨39, by decide⟩).energy) (xi := (166515401487751 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12739 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12739]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12739])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12739) (a := (82730008038871 / 100000000000000 : ℝ)) (b := (80843393969 / 50000000000000 : ℝ)) (q := (2246864980131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12739])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12739]

theorem cert12740_20 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (20845209009621 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (17973340143 / 800000000000 : ℝ))
      (E := (cell12740 ⟨20, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (20845209009621 / 25000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (17973340143 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_21 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83346365421287 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246671503493 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨21, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83346365421287 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246671503493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_22 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (3332476761047 / 4000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246675497603 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨22, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (3332476761047 / 4000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246675497603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_23 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83277496820301 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (28083493799 / 1250000000000 : ℝ))
      (E := (cell12740 ⟨23, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83277496820301 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (28083493799 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_24 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41621549385493 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (14041772037 / 625000000000 : ℝ))
      (E := (cell12740 ⟨24, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41621549385493 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (14041772037 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_25 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83208724845717 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (44933750169 / 2000000000000 : ℝ))
      (E := (cell12740 ⟨25, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83208724845717 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (44933750169 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_26 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83174375012151 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246691512869 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨26, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83174375012151 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246691512869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_27 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83140049238109 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123347770977 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨27, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83140049238109 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123347770977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_28 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (10388218436447 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123349769889 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨28, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (10388218436447 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123349769889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_29 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83071469740701 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449340701717 / 20000000000000 : ℝ))
      (E := (cell12740 ⟨29, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83071469740701 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (449340701717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_30 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41518607976899 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246707508899 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨30, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41518607976899 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246707508899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_31 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (83002986099339 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (140419471411 / 6250000000000 : ℝ))
      (E := (cell12740 ⟨31, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (83002986099339 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (140419471411 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_32 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (2074219503649 / 2500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (89868622107 / 4000000000000 : ℝ))
      (E := (cell12740 ⟨32, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (2074219503649 / 2500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (89868622107 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_33 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41467299031227 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123359770261 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨33, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41467299031227 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123359770261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_34 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41450219908887 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246723565827 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨34, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41450219908887 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246723565827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_35 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (10358288172629 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246727570899 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨35, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (10358288172629 / 12500000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246727570899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_36 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82832194721493 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (224673155639 / 10000000000000 : ℝ))
      (E := (cell12740 ⟨36, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82832194721493 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (224673155639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_37 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82798107808583 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123367761361 / 50000000000000 : ℝ))
      (E := (cell12740 ⟨37, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82798107808583 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (1123367761361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_38 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (41382022305939 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246739528803 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨38, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (41382022305939 / 50000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246739528803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12740_39 : CellCertificate 12740 (3542305787003 / 40000000000000 : ℝ) (1648697568311329 / 1000000000000000000 : ℝ) (41625503623437 / 1250000000000000 : ℝ)
    (cell12740 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · norm_num [cell12740]
  · have h := gap_lower (n := 12740) (a := (82730005101111 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246743574683 / 100000000000000 : ℝ))
      (E := (cell12740 ⟨39, by decide⟩).energy) (xi := (41625503623437 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12740 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12740]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12740])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12740) (a := (82730005101111 / 100000000000000 : ℝ)) (b := (161673942903 / 100000000000000 : ℝ)) (q := (2246743574683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12740])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12740]

theorem cert12741_20 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83380827290857 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246546141611 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨20, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83380827290857 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246546141611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_21 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20836589245833 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246550109931 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨21, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20836589245833 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246550109931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_22 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83311910897461 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246554145779 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨22, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83311910897461 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246554145779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_23 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20819372250099 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123279068117 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨23, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20819372250099 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123279068117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_24 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (4162154562973 / 5000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (56164053577 / 2500000000000 : ℝ))
      (E := (cell12741 ⟨24, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (4162154562973 / 5000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (56164053577 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_25 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41604358821071 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123283055579 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨25, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41604358821071 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123283055579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_26 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41587184058049 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246570160253 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨26, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41587184058049 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246570160253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_27 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83140042649151 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246574117869 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨27, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83140042649151 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246574117869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_28 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41552870604643 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246578161821 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨28, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41552870604643 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246578161821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_29 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41535731882327 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246582177503 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨29, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41535731882327 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246582177503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_30 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (5189825642723 / 6250000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561646541731 / 25000000000000 : ℝ))
      (E := (cell12741 ⟨30, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (5189825642723 / 6250000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (561646541731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_31 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (83002980734503 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123295065933 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨31, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (83002980734503 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123295065933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_32 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41484387543047 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123297066223 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨32, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41484387543047 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123297066223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_33 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (16586918661427 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112329908503 / 5000000000000 : ℝ))
      (E := (cell12741 ⟨33, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (16586918661427 / 20000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (112329908503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_34 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41450217683291 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449320437453 / 20000000000000 : ℝ))
      (E := (cell12741 ⟨34, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41450217683291 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (449320437453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_35 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (10358287654193 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280825773117 / 12500000000000 : ℝ))
      (E := (cell12741 ⟨35, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (10358287654193 / 12500000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (280825773117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_36 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82832190877291 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123305081859 / 50000000000000 : ℝ))
      (E := (cell12741 ⟨36, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82832190877291 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (1123305081859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_37 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (41399052133623 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (7020669321 / 312500000000 : ℝ))
      (E := (cell12741 ⟨37, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (41399052133623 / 50000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (7020669321 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_38 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (20691010343247 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246618183507 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨38, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (20691010343247 / 25000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246618183507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12741_39 : CellCertificate 12741 (885548680275353 / 10000000000000000 : ℝ) (1648568124947287 / 1000000000000000000 : ℝ) (83244314840077 / 2500000000000000 : ℝ)
    (cell12741 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · norm_num [cell12741]
  · have h := gap_lower (n := 12741) (a := (82730002164251 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246622166059 / 100000000000000 : ℝ))
      (E := (cell12741 ⟨39, by decide⟩).energy) (xi := (83244314840077 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12741 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12741]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12741])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12741) (a := (82730002164251 / 100000000000000 : ℝ)) (b := (40415274981 / 25000000000000 : ℝ)) (q := (2246622166059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12741])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12741]

theorem cert12742_20 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (8338081854483 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449284952291 / 20000000000000 : ℝ))
      (E := (cell12742 ⟨20, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (8338081854483 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449284952291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_21 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (4167317427347 / 5000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246428770821 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨21, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (4167317427347 / 5000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246428770821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_22 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (2603496961571 / 3125000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (112321639507 / 5000000000000 : ℝ))
      (E := (cell12742 ⟨22, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (2603496961571 / 3125000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (112321639507 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_23 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (4163874059099 / 5000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561609191193 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨23, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (4163874059099 / 5000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561609191193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_24 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41621541874693 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561610203719 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨24, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41621541874693 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561610203719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_25 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41604355219991 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246444768563 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨25, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41604355219991 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246444768563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_26 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83174361221423 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561612200993 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨26, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83174361221423 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561612200993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_27 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83140036061533 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246452807053 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨27, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83140036061533 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246452807053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_28 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83105734928299 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246456780277 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨28, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83105734928299 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246456780277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_29 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (5191966111867 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246460784379 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨29, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (5191966111867 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246460784379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_30 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (83037204614567 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123232410719 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨30, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (83037204614567 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123232410719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_31 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41501487685429 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561617208691 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨31, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41501487685429 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561617208691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_32 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (41484385013691 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246472825911 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨32, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (41484385013691 / 50000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246472825911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_33 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (16586917710587 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246476796201 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨33, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (16586917710587 / 20000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246476796201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_34 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (8290043091647 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449296161069 / 20000000000000 : ℝ))
      (E := (cell12742 ⟨34, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (8290043091647 / 10000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (449296161069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_35 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82866297087101 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561621213571 / 25000000000000 : ℝ))
      (E := (cell12742 ⟨35, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82866297087101 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (561621213571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_36 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (5177011689631 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246488826421 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨36, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (5177011689631 / 6250000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246488826421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_37 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (517488129543 / 625000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246492839471 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨37, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (517488129543 / 625000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246492839471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_38 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (82764038135033 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123248417501 / 50000000000000 : ℝ))
      (E := (cell12742 ⟨38, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (82764038135033 / 100000000000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (1123248417501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12742_39 : CellCertificate 12742 (44276045899163 / 500000000000000 : ℝ) (1648438701907491 / 1000000000000000000 : ℝ) (66590098818557 / 2000000000000000 : ℝ)
    (cell12742 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · norm_num [cell12742]
  · have h := gap_lower (n := 12742) (a := (646328118971 / 781250000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246500871719 / 100000000000000 : ℝ))
      (E := (cell12742 ⟨39, by decide⟩).energy) (xi := (66590098818557 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12742 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12742]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12742])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12742) (a := (646328118971 / 781250000000 : ℝ)) (b := (80824129499 / 50000000000000 : ℝ)) (q := (2246500871719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12742])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12742]

theorem cert12743_20 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16676161960081 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (561575873493 / 25000000000000 : ℝ))
      (E := (cell12743 ⟨20, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16676161960081 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (561575873493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_21 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (5209146257007 / 6250000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246307486163 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨21, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (5209146257007 / 6250000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246307486163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_22 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (8331189464461 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123155744507 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨22, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (8331189464461 / 10000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123155744507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_23 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20819368341263 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246315506239 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨23, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20819368341263 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246315506239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_24 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (83243076240763 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123159741467 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨24, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (83243076240763 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123159741467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_25 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16641740647847 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246323480669 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨25, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16641740647847 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246323480669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_26 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20793588582031 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123163751227 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨26, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20793588582031 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123163751227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_27 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41570014737627 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246331492613 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨27, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41570014737627 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246331492613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_28 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41552864324307 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280791939011 / 12500000000000 : ℝ))
      (E := (cell12743 ⟨28, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41552864324307 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280791939011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_29 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20767862954089 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123169752347 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨29, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20767862954089 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123169752347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_30 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41518599473397 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123171765479 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨30, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41518599473397 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123171765479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_31 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16600594001681 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (224634753419 / 10000000000000 : ℝ))
      (E := (cell12743 ⟨31, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16600594001681 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (224634753419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_32 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41484382484913 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246351515939 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨32, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41484382484913 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246351515939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_33 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20733645949963 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246355536119 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨33, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20733645949963 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246355536119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_34 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (1036255330843 / 1250000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123179768643 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨34, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (1036255330843 / 1250000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123179768643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_35 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (41433146470851 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (224636352031 / 10000000000000 : ℝ))
      (E := (cell12743 ⟨35, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (41433146470851 / 50000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (224636352031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_36 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (82832183191909 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (140397971531 / 6250000000000 : ℝ))
      (E := (cell12743 ⟨36, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (82832183191909 / 100000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (140397971531 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_37 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (16559619437497 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246371551657 / 100000000000000 : ℝ))
      (E := (cell12743 ⟨37, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (16559619437497 / 20000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (2246371551657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_38 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (20691008724503 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280796942749 / 12500000000000 : ℝ))
      (E := (cell12743 ⟨38, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (20691008724503 / 25000000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (280796942749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12743_39 : CellCertificate 12743 (885493159873481 / 10000000000000000 : ℝ) (824154649593577 / 500000000000000000 : ℝ) (332923733183773 / 10000000000000000 : ℝ)
    (cell12743 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · norm_num [cell12743]
  · have h := gap_lower (n := 12743) (a := (10341249536653 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123189757739 / 50000000000000 : ℝ))
      (E := (cell12743 ⟨39, by decide⟩).energy) (xi := (332923733183773 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12743 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12743]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12743])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12743) (a := (10341249536653 / 12500000000000 : ℝ)) (b := (1293083361 / 800000000000 : ℝ)) (q := (1123189757739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12743])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12743]

theorem cert12744_20 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (4169040052879 / 5000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561545555649 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨20, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (4169040052879 / 5000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561545555649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_21 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83346331678847 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561546549413 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨21, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83346331678847 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561546549413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_22 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (10413985815059 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89847607363 / 4000000000000 : ℝ))
      (E := (cell12744 ⟨22, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (10413985815059 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89847607363 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_23 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20819366387403 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89847767423 / 4000000000000 : ℝ))
      (E := (cell12744 ⟨23, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20819366387403 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89847767423 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_24 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83243068733591 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246198205629 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨24, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83243068733591 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246198205629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_25 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83208696039901 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89848087563 / 4000000000000 : ℝ))
      (E := (cell12744 ⟨25, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83208696039901 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (89848087563 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_26 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83174347436201 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246206197273 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨26, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83174347436201 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246206197273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_27 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (16628004578063 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449242046599 / 20000000000000 : ℝ))
      (E := (cell12744 ⟨27, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (16628004578063 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449242046599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_28 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (10388215296279 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246214240311 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨28, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (10388215296279 / 12500000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246214240311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_29 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (16614289168821 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (112310911073 / 5000000000000 : ℝ))
      (E := (cell12744 ⟨29, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (16614289168821 / 20000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (112310911073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_30 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (332148773121 / 400000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280777779621 / 12500000000000 : ℝ))
      (E := (cell12744 ⟨30, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (332148773121 / 400000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (280777779621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_31 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (83002964647143 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123113115071 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨31, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (83002964647143 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123113115071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_32 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82968759913423 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123115130549 / 50000000000000 : ℝ))
      (E := (cell12744 ⟨32, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82968759913423 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (1123115130549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_33 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82934579047887 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246234214053 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨33, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82934579047887 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246234214053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_34 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82900422019491 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246238265867 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨34, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82900422019491 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246238265867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_35 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (20716572199337 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (140390140103 / 6250000000000 : ℝ))
      (E := (cell12744 ⟨35, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (20716572199337 / 25000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (140390140103 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_36 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (82832179350729 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246246259287 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨36, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (82832179350729 / 100000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246246259287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_37 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41399046824531 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449250052119 / 20000000000000 : ℝ))
      (E := (cell12744 ⟨37, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41399046824531 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (449250052119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_38 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41382015830963 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561563561443 / 25000000000000 : ℝ))
      (E := (cell12744 ⟨38, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41382015830963 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (561563561443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12744_39 : CellCertificate 12744 (35418616237801 / 400000000000000 : ℝ) (412044979195373 / 250000000000000000 : ℝ) (8322424415803 / 250000000000000 : ℝ)
    (cell12744 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · norm_num [cell12744]
  · have h := gap_lower (n := 12744) (a := (41364996679529 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246258273521 / 100000000000000 : ℝ))
      (E := (cell12744 ⟨39, by decide⟩).energy) (xi := (8322424415803 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12744 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12744]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12744])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12744) (a := (41364996679529 / 50000000000000 : ℝ)) (b := (80811291653 / 50000000000000 : ℝ)) (q := (2246258273521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12744])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12744]

theorem cert12745_20 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (16676158463271 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246060947331 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨20, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (16676158463271 / 20000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246060947331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_21 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (10418290405893 / 12500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449212992719 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨21, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (10418290405893 / 12500000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449212992719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_22 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (4165593919893 / 5000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246068991981 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨22, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (4165593919893 / 5000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246068991981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_23 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (4163872886783 / 5000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246072977843 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨23, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (4163872886783 / 5000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246072977843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_24 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (8324306122787 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246076982963 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨24, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (8324306122787 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246076982963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_25 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83208688841981 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246080952181 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨25, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83208688841981 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246080952181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_26 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41587170272827 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449216989371 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨26, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41587170272827 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449216989371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_27 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41570008153357 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449217793951 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨27, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41570008153357 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449217793951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_28 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83105716093151 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246092964951 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨28, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83105716093151 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246092964951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_29 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83071439873119 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123048496587 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨29, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83071439873119 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123048496587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_30 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (83037187614933 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123050498993 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨30, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (83037187614933 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123050498993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_31 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (2593842477721 / 3125000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449220996233 / 20000000000000 : ℝ))
      (E := (cell12745 ⟨31, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (2593842477721 / 3125000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (449220996233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_32 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (3318750194327 / 4000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246109002823 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨32, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (3318750194327 / 4000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246109002823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_33 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82934574297039 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123056502883 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨33, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82934574297039 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123056502883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_34 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41450208786311 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224611699109 / 10000000000000 : ℝ))
      (E := (cell12745 ⟨34, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41450208786311 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (224611699109 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_35 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82866284654037 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246121018301 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨35, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82866284654037 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246121018301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_36 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82832175510557 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246125029453 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨36, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82832175510557 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246125029453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_37 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (82798090111609 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246129024969 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨37, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (82798090111609 / 100000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246129024969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_38 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (41382014213387 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246133005049 / 100000000000000 : ℝ))
      (E := (cell12745 ⟨38, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (41382014213387 / 50000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (2246133005049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12745_39 : CellCertificate 12745 (8854376561969 / 100000000000000 : ℝ) (824025277342861 / 500000000000000000 : ℝ) (332870224436673 / 10000000000000000 : ℝ)
    (cell12745 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · norm_num [cell12745]
  · have h := gap_lower (n := 12745) (a := (8272999042579 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123068514197 / 50000000000000 : ℝ))
      (E := (cell12745 ⟨39, by decide⟩).energy) (xi := (332870224436673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12745 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12745]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12745])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12745) (a := (8272999042579 / 10000000000000 : ℝ)) (b := (161609748539 / 100000000000000 : ℝ)) (q := (1123068514197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12745])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12745]

theorem cert12746_20 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83380783576729 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245939726459 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨20, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83380783576729 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245939726459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_21 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83346314817003 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245943725687 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨21, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83346314817003 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245943725687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_22 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83311870276773 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245947737743 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨22, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83311870276773 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245947737743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_23 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20819362480799 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449190353267 / 20000000000000 : ℝ))
      (E := (cell12746 ⟨23, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20819362480799 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449190353267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_24 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41621526861799 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122977878281 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨24, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41621526861799 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122977878281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_25 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41604340822737 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245959769989 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨25, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41604340822737 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245959769989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_26 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83174333656483 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245963751199 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨26, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83174333656483 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245963751199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_27 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20785002431113 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122983880669 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨27, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20785002431113 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122983880669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_28 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20776427454343 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (89838869779 / 4000000000000 : ℝ))
      (E := (cell12746 ⟨28, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20776427454343 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (89838869779 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_29 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (83071433903397 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245975761341 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨29, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (83071433903397 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245975761341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_30 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20759295487711 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449195951099 / 20000000000000 : ℝ))
      (E := (cell12746 ⟨30, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20759295487711 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (449195951099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_31 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (162115144391 / 195312500000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (280747973407 / 12500000000000 : ℝ))
      (E := (cell12746 ⟨31, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (162115144391 / 195312500000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (280747973407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_32 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82968749804081 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122993899839 / 50000000000000 : ℝ))
      (E := (cell12746 ⟨32, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82968749804081 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (1122993899839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_33 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20733642386827 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561497948521 / 25000000000000 : ℝ))
      (E := (cell12746 ⟨33, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20733642386827 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (561497948521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_34 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82900413126833 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245995771567 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨34, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82900413126833 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245995771567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_35 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (8286628051177 / 10000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245999791633 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨35, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (8286628051177 / 10000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2245999791633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_36 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (2588505364731 / 3125000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (140375237271 / 6250000000000 : ℝ))
      (E := (cell12746 ⟨36, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (2588505364731 / 3125000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (140375237271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_37 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (41399043287563 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246007786099 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨37, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (41399043287563 / 50000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246007786099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_38 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (20691006298139 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246011819823 / 100000000000000 : ℝ))
      (E := (cell12746 ⟨38, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (20691006298139 / 25000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (2246011819823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12746_39 : CellCertificate 12746 (885409910628119 / 10000000000000000 : ℝ) (823960606447531 / 500000000000000000 : ℝ) (8321086914907 / 250000000000000 : ℝ)
    (cell12746 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · norm_num [cell12746]
  · have h := gap_lower (n := 12746) (a := (82729987493419 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (89840633553 / 4000000000000 : ℝ))
      (E := (cell12746 ⟨39, by decide⟩).energy) (xi := (8321086914907 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12746 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12746]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12746])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12746) (a := (82729987493419 / 100000000000000 : ℝ)) (b := (6463876633 / 4000000000000 : ℝ)) (q := (89840633553 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12746])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12746]

theorem cert12747_20 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83380774838703 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122909279991 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨20, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83380774838703 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122909279991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_21 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10418288298553 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245822600543 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨21, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10418288298553 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245822600543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_22 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83311862157209 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561456649089 / 25000000000000 : ℝ))
      (E := (cell12747 ⟨22, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83311862157209 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (561456649089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_23 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41638721056109 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245830551057 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨23, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41638721056109 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245830551057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_24 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10405380777597 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245834584803 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨24, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10405380777597 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245834584803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_25 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83208674450379 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122919292051 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨25, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83208674450379 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122919292051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_26 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83174326768687 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224584261031 / 10000000000000 : ℝ))
      (E := (cell12747 ⟨26, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83174326768687 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (224584261031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_27 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10392500392941 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (8983386431 / 400000000000 : ℝ))
      (E := (cell12747 ⟨27, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10392500392941 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (8983386431 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_28 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41552851771447 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245850578889 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨28, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41552851771447 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245850578889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_29 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (83071427934939 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245854584459 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨29, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (83071427934939 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245854584459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_30 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41518588143991 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122929313267 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨30, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41518588143991 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122929313267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_31 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41501474285251 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (56146564747 / 2500000000000 : ℝ))
      (E := (cell12747 ⟨31, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41501474285251 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (56146564747 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_32 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (4148437237557 / 5000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (140366662069 / 6250000000000 : ℝ))
      (E := (cell12747 ⟨32, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (4148437237557 / 5000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (140366662069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_33 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41467282399347 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245870637597 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨33, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41467282399347 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245870637597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_34 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (20725102170531 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245874607301 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨34, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (20725102170531 / 25000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245874607301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_35 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41433138185273 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122939310141 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨35, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41433138185273 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122939310141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_36 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (82832167833233 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122941309299 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨36, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (82832167833233 / 100000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122941309299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_37 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (41399041519807 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122943301333 / 50000000000000 : ℝ))
      (E := (cell12747 ⟨37, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (41399041519807 / 50000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (1122943301333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_38 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (10345502744909 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245890631391 / 100000000000000 : ℝ))
      (E := (cell12747 ⟨38, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (10345502744909 / 12500000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (2245890631391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12747_39 : CellCertificate 12747 (88538216923769 / 1000000000000000 : ℝ) (164779189140473 / 100000000000000000 : ℝ) (33281673310979 / 1000000000000000 : ℝ)
    (cell12747 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · norm_num [cell12747]
  · have h := gap_lower (n := 12747) (a := (16545996912389 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280736830761 / 12500000000000 : ℝ))
      (E := (cell12747 ⟨39, by decide⟩).energy) (xi := (33281673310979 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12747 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12747]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12747])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12747) (a := (16545996912389 / 20000000000000 : ℝ)) (b := (161584085161 / 100000000000000 : ℝ)) (q := (280736830761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12747])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12747]

theorem cert12748_20 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (3335230644091 / 4000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245697447901 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨20, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (3335230644091 / 4000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245697447901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_21 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41673148980703 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245701413243 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨21, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41673148980703 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245701413243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_22 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (8331185403917 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561426362789 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨22, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (8331185403917 / 10000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561426362789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_23 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83277434302727 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245709448711 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨23, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83277434302727 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245709448711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_24 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83243038719403 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (224571340931 / 10000000000000 : ℝ))
      (E := (cell12748 ⟨24, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83243038719403 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (224571340931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_25 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10401083407087 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122858726459 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨25, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10401083407087 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122858726459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_26 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41587159941133 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122860732881 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨26, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41587159941133 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122860732881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_27 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41569998281971 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245725450541 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨27, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41569998281971 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245725450541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_28 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83105697269717 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (224572946819 / 10000000000000 : ℝ))
      (E := (cell12748 ⟨28, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83105697269717 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (224572946819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_29 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (16614284393549 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (89829338501 / 4000000000000 : ℝ))
      (E := (cell12748 ⟨29, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (16614284393549 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (89829338501 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_30 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (83037170626347 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245737435547 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨30, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (83037170626347 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245737435547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_31 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (41501471607001 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280717680947 / 12500000000000 : ℝ))
      (E := (cell12748 ⟨31, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (41501471607001 / 50000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (280717680947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_32 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (10371092462419 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122872720831 / 50000000000000 : ℝ))
      (E := (cell12748 ⟨32, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (10371092462419 / 12500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (1122872720831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_33 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (20733640012799 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561437369429 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨33, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (20733640012799 / 25000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561437369429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_34 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (16580080847699 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245753439677 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨34, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (16580080847699 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245753439677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_35 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (16573254446073 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245757445613 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨35, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (16573254446073 / 20000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245757445613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_36 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82832163996081 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561440374059 / 25000000000000 : ℝ))
      (E := (cell12748 ⟨36, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82832163996081 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (561440374059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_37 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82798079505071 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245765474673 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨37, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82798079505071 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245765474673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_38 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (2069100468173 / 2500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (112288474923 / 5000000000000 : ℝ))
      (E := (cell12748 ⟨38, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (2069100468173 / 2500000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (112288474923 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12748_39 : CellCertificate 12748 (7082835456197 / 80000000000000 : ℝ) (1647662590209949 / 1000000000000000000 : ℝ) (332789993976053 / 10000000000000000 : ℝ)
    (cell12748 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · norm_num [cell12748]
  · have h := gap_lower (n := 12748) (a := (82729981631367 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245773508911 / 100000000000000 : ℝ))
      (E := (cell12748 ⟨39, by decide⟩).energy) (xi := (332789993976053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12748 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12748]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12748])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12748) (a := (82729981631367 / 100000000000000 : ℝ)) (b := (161571256549 / 100000000000000 : ℝ)) (q := (2245773508911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12748])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12748]

theorem cert12749_20 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41690378683723 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122788165967 / 50000000000000 : ℝ))
      (E := (cell12749 ⟨20, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41690378683723 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1122788165967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_21 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (83346289535949 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245580338709 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨21, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (83346289535949 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245580338709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_22 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41655922961327 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561396075537 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨22, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41655922961327 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561396075537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_23 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41638713247361 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449117668519 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨23, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41638713247361 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449117668519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_24 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (2081075780487 / 2500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245592346837 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨24, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (2081075780487 / 2500000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245592346837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_25 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (3328346402577 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245596318039 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨25, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (3328346402577 / 4000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245596318039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_26 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (4158715649861 / 5000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245600317557 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨26, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (4158715649861 / 5000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245600317557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_27 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41569994992847 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1754378397 / 78125000000 : ℝ))
      (E := (cell12749 ⟨27, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41569994992847 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (1754378397 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_28 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (1038821137473 / 1250000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280701044239 / 12500000000000 : ℝ))
      (E := (cell12749 ⟨28, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (1038821137473 / 1250000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280701044239 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_29 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16614283200363 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245612337049 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨29, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16614283200363 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245612337049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_30 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41518582482969 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561404089523 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨30, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41518582482969 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561404089523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_31 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (20750734464673 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449124072069 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨31, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (20750734464673 / 25000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449124072069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_32 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82968734648717 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561406086339 / 25000000000000 : ℝ))
      (E := (cell12749 ⟨32, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82968734648717 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (561406086339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_33 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41467277652407 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280703546629 / 12500000000000 : ℝ))
      (E := (cell12749 ⟨33, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41467277652407 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (280703546629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_34 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16580079959189 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (140352020457 / 6250000000000 : ℝ))
      (E := (cell12749 ⟨34, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16580079959189 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (140352020457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_35 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82866268091227 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245636384897 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨35, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82866268091227 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245636384897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_36 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (16566432031987 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449128074119 / 20000000000000 : ℝ))
      (E := (cell12749 ⟨36, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (16566432031987 / 20000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (449128074119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_37 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41399037985749 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245644343437 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨37, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41399037985749 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245644343437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_38 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (41382007747751 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245648362323 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨38, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (41382007747751 / 50000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245648362323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

theorem cert12749_39 : CellCertificate 12749 (442663349493967 / 5000000000000000 : ℝ) (1647533309305941 / 1000000000000000000 : ℝ) (332763259193917 / 10000000000000000 : ℝ)
    (cell12749 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · norm_num [cell12749]
  · have h := gap_lower (n := 12749) (a := (82729978701687 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245652368567 / 100000000000000 : ℝ))
      (E := (cell12749 ⟨39, by decide⟩).energy) (xi := (332763259193917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12749 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12749]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12749])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12749) (a := (82729978701687 / 100000000000000 : ℝ)) (b := (161558429987 / 100000000000000 : ℝ)) (q := (2245652368567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12749])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12749]

end BstLean.Part268
